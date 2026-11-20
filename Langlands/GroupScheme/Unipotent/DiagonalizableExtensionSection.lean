import Langlands.GroupScheme.Torus.MultiplicativeTypeConnectedActionProof
import Langlands.GroupScheme.ActionDescent
import Langlands.GroupScheme.RepresentedAction
import Langlands.GroupScheme.Torus.CentralDiagonalizableExtensionSplit
import Langlands.GroupScheme.HomDescent
import Langlands.GroupScheme.AffineNormalSubgroupQuotientProof
import Langlands.Algebra.CentralExtensionSectionHopf
import Langlands.GroupScheme.HopfPrimitiveQuotient
import Langlands.GroupScheme.Unipotent.PerfectFieldSplitProof
import Langlands.GroupScheme.Unipotent.SplitAffineSpaceProof
import Langlands.GroupScheme.Unipotent.MultiplicativeTrivialityProof
import Langlands.GroupScheme.SemidirectProduct

/-! # Extensions of a unipotent group by a diagonalizable group

Centrality of the kernel, affineness of the quotient, and existence and uniqueness of a
homomorphic section, for an fppf quotient map `q : G ⟶ U` over a field whose kernel is a
diagonalizable group `D` (Milne, *Algebraic Groups* (2017), Proposition 16.28). -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct Coalgebra
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.DiagonalizableUnipotentExtension

open RelativeRoot

variable {k : Type u} [Field k] {G D U : GroupScheme (Spec (CommRingCat.of k))}

/-- Conjugation in `G` preserves the kernel of an fppf quotient map. -/
theorem conjugation_isStable (i : D ⟶ G) {q : G ⟶ U}
    (hq : IsFppfQuotient (SubgroupFunctor.range i) q) :
    (AutomorphicAction.conjugation (𝟙 G)).IsStable (SubgroupFunctor.range i) := by
  intro T g x hx
  rw [← hq.2.2.2] at hx ⊢
  rw [mem_range_kernelι_iff] at hx ⊢
  simp only [AutomorphicAction.conjugation_act, Grp.id_hom_hom, Category.comp_id,
    MonObj.mul_comp, GrpObj.inv_comp, hx, mul_one, mul_inv_cancel]

/-- **Centrality.** Let `q : G ⟶ U` be an fppf quotient map, quasi-compact, whose kernel is
represented by `i : D ⟶ G` with `D` of multiplicative type. If `U` is connected, quasi-compact
and locally of finite type, then `D` is central in `G`: conjugation by `G` on `D` is trivial on
`D` itself (it is commutative), hence descends to an action of `U` on `D`, which is trivial by
rigidity of groups of multiplicative type. -/
theorem isCentral (i : D ⟶ G) (q : G ⟶ U) [Mono i.hom.hom]
    (hq : IsFppfQuotient (SubgroupFunctor.range i) q) [QuasiCompact q.hom.hom.left]
    (hD : IsMultiplicativeType D) (hUt : LocallyOfFiniteType U.X.hom)
    (hUq : QuasiCompact U.X.hom) (hUc : ConnectedSpace U.X.left) : IsCentral i := by
  have : IsCommMonObj D.X := hD.isCommMonObj
  have : Flat q.hom.hom.left := hq.1
  have : Surjective q.hom.hom.left := hq.2.1
  let a0 : AutomorphicAction G G := AutomorphicAction.conjugation (𝟙 G)
  have hrep : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨inferInstance, rfl⟩
  let a1 : AutomorphicAction G D := a0.onRepresentedSubgroup i hrep (conjugation_isStable i hq)
  have ha1 : ∀ {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ G.X) (d : T ⟶ D.X),
      a1.act g d ≫ i.hom.hom = g * (d ≫ i.hom.hom) * g⁻¹ := by
    intro T g d
    rw [AutomorphicAction.onRepresentedSubgroup_act_comp]
    simp only [a0, AutomorphicAction.conjugation_act, Grp.id_hom_hom, Category.comp_id]
  have hk : AutomorphicAction.KernelActsTrivially a1 q := by
    intro T x d
    apply (cancel_mono i.hom.hom).1
    rw [AutomorphicAction.restrict_act, ha1]
    have hx : x ≫ (kernelι q).hom.hom ∈ (SubgroupFunctor.range i).carrier T := by
      rw [← hq.2.2.2]
      exact SubgroupFunctor.mem_range.2 ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.1 hx
    rw [← hy, ← MonObj.mul_comp, ← GrpObj.inv_comp, ← MonObj.mul_comp, mul_comm y d,
      mul_inv_cancel_right]
  let a2 : AutomorphicAction U D := AutomorphicAction.quotientAction a1 q hk
  have htriv := (multiplicativeTypeConnectedAction k U D hUt hUq hUc hD).1 a2
  intro T g
  rw [mem_center]
  intro T' b h
  have e := htriv T' (h ≫ q.hom.hom) (b ≫ g)
  rw [AutomorphicAction.quotientAction_act_lift] at e
  have e' := congrArg (· ≫ i.hom.hom) e
  simp only [ha1] at e'
  -- e' : h * ((b ≫ g) ≫ i) * h⁻¹ = (b ≫ g) ≫ i
  rw [Category.assoc] at e'
  show (b ≫ g ≫ i.hom.hom) * h = h * (b ≫ g ≫ i.hom.hom)
  calc (b ≫ g ≫ i.hom.hom) * h = (h * (b ≫ g ≫ i.hom.hom) * h⁻¹) * h := by rw [e']
    _ = h * (b ≫ g ≫ i.hom.hom) := by rw [inv_mul_cancel_right]

/-- A homomorphism kills the kernel of `q` when its own kernel contains it. -/
theorem kernelι_comp_eq_zero {Q Q' : GroupScheme (Spec (CommRingCat.of k))} (q : G ⟶ Q)
    (q' : G ⟶ Q')
    (h : SubgroupFunctor.range (kernelι q) ≤ SubgroupFunctor.range (kernelι q')) :
    kernelι q ≫ q' = 0 := by
  apply Grp.hom_ext
  change (kernelι q).hom.hom ≫ q'.hom.hom = 1
  apply (mem_range_kernelι_iff q' _).mp
  apply h (kernel q).X
  exact SubgroupFunctor.mem_range.2 ⟨𝟙 (kernel q).X, Category.id_comp _⟩

/-- Two fpqc quotient maps with the same kernel have isomorphic targets. -/
def quotientIso {Q Q' : GroupScheme (Spec (CommRingCat.of k))} (q : G ⟶ Q) (q' : G ⟶ Q')
    [QuasiCompact q.hom.hom.left] [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [QuasiCompact q'.hom.hom.left] [Flat q'.hom.hom.left] [Surjective q'.hom.hom.left]
    (h : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range (kernelι q')) : Q ≅ Q' where
  hom := FpqcHomDescent.hom q q' (kernelι_comp_eq_zero q q' h.le)
  inv := FpqcHomDescent.hom q' q (kernelι_comp_eq_zero q' q h.ge)
  hom_inv_id := by
    have h0 := kernelι_comp_eq_zero q q le_rfl
    rw [FpqcHomDescent.unique q q h0 (𝟙 Q) (Category.comp_id q)]
    apply FpqcHomDescent.unique q q h0
    rw [← Category.assoc, FpqcHomDescent.fac, FpqcHomDescent.fac]
  inv_hom_id := by
    have h0 := kernelι_comp_eq_zero q' q' le_rfl
    rw [FpqcHomDescent.unique q' q' h0 (𝟙 Q') (Category.comp_id q')]
    apply FpqcHomDescent.unique q' q' h0
    rw [← Category.assoc, FpqcHomDescent.fac, FpqcHomDescent.fac]

/-- An fppf quotient map whose kernel is represented by an affine group is affine. -/
theorem isAffineHom_quotientMap (i : D ⟶ G) [Mono i.hom.hom] {q : G ⟶ U}
    (hq : IsFppfQuotient (SubgroupFunctor.range i) q) [IsAffineHom D.X.hom] :
    IsAffineHom q.hom.hom.left :=
  hq.isAffineHom_of_isAffineHom_kernel i

/-- **Affineness of the quotient.** Over a field, the target of an fppf quotient map of an
affine group locally of finite type by a closed subgroup with affine total space is affine:
it is isomorphic to the published affine quotient. -/
theorem isAffineHom_quotient [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]
    (i : D ⟶ G) (q : G ⟶ U) (hi : IsClosedSubgroup i)
    (hq : IsFppfQuotient (SubgroupFunctor.range i) q) [IsAffineHom D.X.hom] :
    IsAffineHom U.X.hom := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have hn : (SubgroupFunctor.range i).IsNormal := by
    rw [← hq.2.2.2]
    exact HopfPrimitive.isNormal_range_kernelι q
  obtain ⟨Q, q', -, hQa, hq'⟩ := affineNormalSubgroupQuotient k G D i hi hn
  have : IsAffineHom q.hom.hom.left := isAffineHom_quotientMap i hq
  have : IsAffineHom q'.hom.hom.left := isAffineHom_quotientMap i hq'
  have : Flat q.hom.hom.left := hq.1
  have : Surjective q.hom.hom.left := hq.2.1
  have : Flat q'.hom.hom.left := hq'.1
  have : Surjective q'.hom.hom.left := hq'.2.1
  exact isAffineHom_of_over_iso ((Grp.forget _).mapIso
    (quotientIso q q' (hq.2.2.2.trans hq'.2.2.2.symm))) hQa

/-! ### Translation to coordinate Hopf algebras -/

section Hopf

open CentralExtensionHopfSpec HopfSpecPoints

variable {K : Type u} [Field K] {Λ : Type u} [AddCommGroup Λ]
  {A B : CommHopfAlgCat.{u} (CommRingCat.of K)}

/-- The Hopf algebra data of a central extension by a diagonalizable group: if `Spec π` is a
central closed subgroup of `Spec A` and `Spec φ` is an fppf quotient map with kernel `Spec π`,
then `φ` and `π` satisfy `CentralExtensionSectionHopf.IsCentralExtension`. -/
theorem isCentralExtension (φ : B ⟶ A)
    (π : A ⟶ Diagonalizable.hopfAlgebra (CommRingCat.of K) Λ)
    (hz : IsClosedSubgroup ((hopfSpec (CommRingCat.of K)).map π.op))
    (hc : IsCentral ((hopfSpec (CommRingCat.of K)).map π.op))
    (hq : IsFppfQuotient (SubgroupFunctor.range ((hopfSpec (CommRingCat.of K)).map π.op))
      ((hopfSpec (CommRingCat.of K)).map φ.op)) :
    CentralExtensionSectionHopf.IsCentralExtension (K := K) (A := A) (B := B) φ.hom π.hom where
  injective := (faithfullyFlat_of_isFppfQuotient φ hq).injective
  surjective := surjective_of_isClosedSubgroup π hz
  comp_eq b := by
    have h := congrArg (fun f => f b) (comp_eq_of_range_kernelι φ π hq.2.2.2)
    simpa using h
  isCentral := rTensor_comul_eq_of_isCentral π hc
  invariants a ha := by
    have : IsClosedImmersion ((hopfSpec (CommRingCat.of K)).map π.op).hom.hom.left := hz
    refine exists_eq_of_lTensor_comul_eq φ π (Over.mono_of_mono_left _) hq a ?_
    rw [GroupAlgebraCoaction.mem_grade_iff, GroupAlgebraCoaction.coaction_apply] at ha
    rw [← (AddMonoidAlgebra.scalarTensorEquiv K A).symm_apply_apply
      ((π.hom : A →ₗ[K] AddMonoidAlgebra K Λ).lTensor A (comul a)), ha,
      AddMonoidAlgebra.scalarTensorEquiv_symm_single, ← AddMonoidAlgebra.one_def]

end Hopf

/-- **Existence of a section from Hopf coordinates.** Let `i : D ⟶ G` be a central closed
subgroup with `D ≅ D_k(Λ)`, and `q : G ⟶ U` an fppf quotient map with kernel `D`, where
`G ≅ Spec A` and `U ≅ Spec B` for commutative Hopf algebras `A` and `B`. If `B` is isomorphic,
as a `k`-algebra, to a polynomial ring over `k`, then `q` has a homomorphic section. -/
theorem exists_section_of_hopf {A B : CommHopfAlgCat.{u} (CommRingCat.of k)}
    (eG : (hopfSpec (CommRingCat.of k)).obj (op A) ≅ G)
    (eU : (hopfSpec (CommRingCat.of k)).obj (op B) ≅ U) {Λ : Type u}
    [AddCommGroup Λ] (eD : D ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp)
    (i : D ⟶ G) (hi : IsClosedSubgroup i) (hc : IsCentral i) (q : G ⟶ U)
    (hq : IsFppfQuotient (SubgroupFunctor.range i) q) {I : Type u}
    (eB : (B : Type u) ≃ₐ[k] MvPolynomial I k) :
    ∃ s : U ⟶ G, s ≫ q = 𝟙 U := by
  let eZ : (hopfSpec (CommRingCat.of k)).obj
      (op (Diagonalizable.hopfAlgebra (CommRingCat.of k) Λ)) ≅ D :=
    Diagonalizable.hopfSpecIso (CommRingCat.of k) Λ ≪≫ eD.symm
  obtain ⟨π, hπ⟩ : ∃ π : A ⟶ Diagonalizable.hopfAlgebra (CommRingCat.of k) Λ,
      (hopfSpec (CommRingCat.of k)).map π.op = eZ.hom ≫ i ≫ eG.symm.hom :=
    ⟨(hopfSpec.fullyFaithful.preimage (eZ.hom ≫ i ≫ eG.symm.hom)).unop,
      hopfSpec.fullyFaithful.map_preimage _⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : B ⟶ A,
      (hopfSpec (CommRingCat.of k)).map φ.op = eG.symm.inv ≫ q ≫ eU.symm.hom :=
    ⟨(hopfSpec.fullyFaithful.preimage (eG.symm.inv ≫ q ≫ eU.symm.hom)).unop,
      hopfSpec.fullyFaithful.map_preimage _⟩
  have hz' : IsClosedSubgroup ((hopfSpec (CommRingCat.of k)).map π.op) := by
    rw [hπ]
    exact IsClosedSubgroup.iso_comp eZ (hi.comp_iso eG.symm)
  have hc' : IsCentral ((hopfSpec (CommRingCat.of k)).map π.op) := by
    rw [hπ]
    exact (hc.comp_iso eG.symm).comp eZ.hom
  have hq' : IsFppfQuotient (SubgroupFunctor.range ((hopfSpec (CommRingCat.of k)).map π.op))
      ((hopfSpec (CommRingCat.of k)).map φ.op) := by
    rw [hπ, hφ, SubgroupFunctor.range_iso_comp, SubgroupFunctor.range_comp_iso,
      ← Category.assoc]
    exact (hq.comapIso eG.symm).comp_iso eU.symm
  have h := isCentralExtension φ π hz' hc' hq'
  obtain ⟨σ, hσ⟩ := CentralExtensionSectionHopf.exists_section_of_algEquiv eB h
  obtain ⟨σc, hσc⟩ : ∃ σc : A ⟶ B, φ ≫ σc = 𝟙 B :=
    ⟨CommHopfAlgCat.ofHom σ, by
      ext b
      exact hσ b⟩
  refine ⟨eU.inv ≫ (hopfSpec (CommRingCat.of k)).map σc.op ≫ eG.hom, ?_⟩
  have hq2 : eG.hom ≫ q = (hopfSpec (CommRingCat.of k)).map φ.op ≫ eU.hom := by
    rw [hφ]
    simp only [Iso.symm_inv, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hcomp : (hopfSpec (CommRingCat.of k)).map σc.op ≫
      (hopfSpec (CommRingCat.of k)).map φ.op = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, ← op_comp, hσc, op_id, CategoryTheory.Functor.map_id]
  rw [Category.assoc, Category.assoc, hq2,
    ← Category.assoc ((hopfSpec (CommRingCat.of k)).map σc.op), hcomp, Category.id_comp,
    Iso.inv_hom_id]

/-- A commutative Hopf algebra whose spectrum is isomorphic, as a scheme over `k`, to an affine
space over `k` is isomorphic, as a `k`-algebra, to the polynomial ring: `Spec` is fully faithful
on `k`-algebras. -/
def algEquivOfAffineSpace {B : CommHopfAlgCat.{u} (CommRingCat.of k)} {I : Type u}
    (e : ((hopfSpec (CommRingCat.of k)).obj (op B)).X ≅
      Over.mk (𝔸(I; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))) :
    (B : Type u) ≃ₐ[k] MvPolynomial I k :=
  let e2 : Over.mk (𝔸(I; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) ≅
      (algSpec (CommRingCat.of k)).obj
        (op (CommAlgCat.of (CommRingCat.of k) (MvPolynomial I (CommRingCat.of k)))) :=
    Over.isoMk (AffineSpace.SpecIso I (CommRingCat.of k)) (by
      rw [algSpec_obj_hom]
      change (AffineSpace.SpecIso I (CommRingCat.of k)).hom ≫
          Spec.map (CommRingCat.ofHom MvPolynomial.C) = 𝔸(I; Spec (CommRingCat.of k)) ↘ _
      rw [← AffineSpace.SpecIso_inv_over, Iso.hom_inv_id_assoc])
  let E : (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) B)) ≅
      (algSpec (CommRingCat.of k)).obj
        (op (CommAlgCat.of (CommRingCat.of k) (MvPolynomial I (CommRingCat.of k)))) :=
    e ≪≫ e2
  CommAlgCat.isoEquivAlgEquiv (algSpec.fullyFaithful.preimageIso E).unop.symm

/-- **Existence of a section.** Over a perfect field, let `i : D ⟶ G` be a central closed
subgroup with `D ≅ D_k(Λ)` and `q : G ⟶ U` an fppf quotient map with kernel `D`, where `G` is
affine and `U` is affine, smooth, connected and unipotent. Then `q` has a homomorphic section:
`U` is split unipotent, hence isomorphic to an affine space as a scheme, so its coordinate
ring is a polynomial ring. -/
theorem exists_section [PerfectField k] [IsAffineHom G.X.hom] [IsAffineHom U.X.hom]
    [Smooth U.X.hom] (hUc : ConnectedSpace U.X.left) (hUu : IsUnipotent U) {Λ : Type u}
    [AddCommGroup Λ] (eD : D ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp)
    (i : D ⟶ G) (hi : IsClosedSubgroup i) (hc : IsCentral i) (q : G ⟶ U)
    (hq : IsFppfQuotient (SubgroupFunctor.range i) q) : ∃ s : U ⟶ G, s ≫ q = 𝟙 U := by
  obtain ⟨n, hn⟩ := perfectFieldUnipotentSplit k U hUc hUu
  obtain ⟨eA⟩ := splitUnipotentAffineSpaceStatement k n U inferInstance hn
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsAffine U.X.left := isAffine_of_isAffineHom U.X.hom
  exact exists_section_of_hopf (AffineCoordinates.hopfSpecIso G)
    (AffineCoordinates.hopfSpecIso U) eD i hi hc q hq
    (algEquivOfAffineSpace ((Grp.forget _).mapIso (AffineCoordinates.hopfSpecIso U) ≪≫ eA))

/-- **Uniqueness of the section.** Let `i : D ⟶ G` be a central monomorphism and `q : G ⟶ U`
an fppf quotient map with kernel `D`, where `U` is unipotent and `D` is of multiplicative type,
both affine and locally of finite type. Two homomorphic sections of `q` agree: their pointwise
quotient is a homomorphism `U ⟶ D`, which is trivial. -/
theorem section_unique [IsAffineHom U.X.hom] [LocallyOfFiniteType U.X.hom]
    [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom] (hU : IsUnipotent U)
    (hD : IsMultiplicativeType D) (i : D ⟶ G) [Mono i.hom.hom] (hc : IsCentral i) (q : G ⟶ U)
    (hq : IsFppfQuotient (SubgroupFunctor.range i) q) (s s' : U ⟶ G) (hs : s ≫ q = 𝟙 U)
    (hs' : s' ≫ q = 𝟙 U) : s' = s := by
  have hmem : s'.hom.hom * (s.hom.hom)⁻¹ ∈ (SubgroupFunctor.range i).carrier U.X := by
    rw [← hq.2.2.2, mem_range_kernelι_iff, MonObj.mul_comp, GrpObj.inv_comp,
      ← Grp.comp_hom_hom, ← Grp.comp_hom_hom, hs, hs', mul_inv_cancel]
  obtain ⟨f, hf⟩ := SubgroupFunctor.mem_range.1 hmem
  have hpt : ∀ {X : Over (Spec (CommRingCat.of k))} (x : X ⟶ U.X),
      x ≫ f ≫ i.hom.hom = (x ≫ s'.hom.hom) * (x ≫ s.hom.hom)⁻¹ := by
    intro X x
    rw [hf, MonObj.comp_mul, GrpObj.comp_inv]
  have hcen : ∀ {X : Over (Spec (CommRingCat.of k))} (z : X ⟶ D.X) (g : X ⟶ G.X),
      Commute (z ≫ i.hom.hom) g := fun z g => commute_of_mem_center (hc _ z) g
  have hmul : ∀ {X : Over (Spec (CommRingCat.of k))} (x y : X ⟶ U.X),
      (x * y) ≫ f = (x ≫ f) * (y ≫ f) := by
    intro X x y
    apply (cancel_mono i.hom.hom).1
    have hc' : Commute (y ≫ f ≫ i.hom.hom) (x ≫ s'.hom.hom) := by
      simpa only [Category.assoc] using hcen (y ≫ f) (x ≫ s'.hom.hom)
    have hc'' : Commute (y ≫ f ≫ i.hom.hom) ((x ≫ s'.hom.hom) * (x ≫ s.hom.hom)⁻¹) := by
      simpa only [Category.assoc] using hcen (y ≫ f) ((x ≫ s'.hom.hom) * (x ≫ s.hom.hom)⁻¹)
    rw [hpt y] at hc' hc''
    calc ((x * y) ≫ f) ≫ i.hom.hom
        = ((x ≫ s'.hom.hom) * (y ≫ s'.hom.hom)) *
            ((x ≫ s.hom.hom) * (y ≫ s.hom.hom))⁻¹ := by
          rw [Category.assoc, hpt, MonObj.mul_comp, MonObj.mul_comp]
      _ = (x ≫ s'.hom.hom) * ((y ≫ s'.hom.hom) * (y ≫ s.hom.hom)⁻¹) *
            (x ≫ s.hom.hom)⁻¹ := by group
      _ = ((y ≫ s'.hom.hom) * (y ≫ s.hom.hom)⁻¹) * (x ≫ s'.hom.hom) *
            (x ≫ s.hom.hom)⁻¹ := by rw [← hc'.eq]
      _ = ((x ≫ s'.hom.hom) * (x ≫ s.hom.hom)⁻¹) *
            ((y ≫ s'.hom.hom) * (y ≫ s.hom.hom)⁻¹) := by rw [mul_assoc, hc''.eq]
      _ = ((x ≫ f) * (y ≫ f)) ≫ i.hom.hom := by
          rw [MonObj.mul_comp, Category.assoc, Category.assoc, hpt, hpt]
  have : IsMonHom f := Semidirect.isMonHom_of_mul_comp f hmul
  let d : U ⟶ D := Grp.homMk f
  have hd := ((unipotentMultiplicativeTriviality k).2.2 U D hU hD).1 d
  apply hom_ext_points
  intro T y
  have hy : y ≫ d.hom.hom ∈ (SubgroupFunctor.range d).carrier T :=
    SubgroupFunctor.mem_range.2 ⟨y, rfl⟩
  rw [hd, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hy
  have hy' : y ≫ f ≫ i.hom.hom = 1 := by
    rw [← Category.assoc]
    change (y ≫ d.hom.hom) ≫ i.hom.hom = 1
    rw [hy, MonObj.one_comp]
  rw [hpt, mul_inv_eq_one] at hy'
  exact hy'

end Langlands.GroupScheme.DiagonalizableUnipotentExtension
