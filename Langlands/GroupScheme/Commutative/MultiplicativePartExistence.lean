import Langlands.GroupScheme.Reductive.UnipotentExtension
import Langlands.GroupScheme.Reductive.UnipotentQuotient
import Langlands.GroupScheme.Absolute.BorelExistenceCoordinates
import Langlands.GroupScheme.Absolute.ParabolicTransport
import Langlands.GroupScheme.Absolute.KernelMaximalTorusUnipotent
import Langlands.GroupScheme.Rational.SubgroupProductGeometry
import Langlands.GroupScheme.Rational.VectorGroupUnipotent
import Langlands.GroupScheme.AffineHomImageProof
import Langlands.GroupScheme.AffineQuotientReduction
import Langlands.GroupScheme.FppfHomDescent
import Langlands.GroupScheme.AffineNormalSubgroupQuotientProof
import Langlands.GroupScheme.UnipotentClosedSubgroupProof
import Langlands.GroupScheme.Torus.MultiplicativeTypeCharacterizationProof
import Langlands.GroupScheme.Torus.MultiplicativeTypeUnipotentHom

/-! # The multiplicative part of a commutative affine algebraic group

Existence of the largest closed subgroup of multiplicative type, with unipotent quotient
(Milne 2017, Theorem 16.13(a), without the characteristic clause). -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Matrix
open CategoryTheory.MonoidalCategory

namespace Langlands.GroupScheme

namespace CommutativeDecomposition

section General

variable {S : Scheme.{u}}

/-- A homomorphism whose underlying point is the identity point is zero. -/
theorem eq_zero_of_hom_eq_one {A B : GroupScheme S} (f : A ⟶ B) (h : f.hom.hom = 1) :
    f = 0 := by
  apply (Grp.forget _).map_injective
  change f.hom.hom = (1 : A.X ⟶ B.X)
  exact h

/-- A homomorphism all of whose points are the identity is zero. -/
theorem eq_zero_of_range_le_kernel {A B : GroupScheme S} (f : A ⟶ B)
    (h : 𝟙 A.X ≫ f.hom.hom = 1) : f = 0 :=
  eq_zero_of_hom_eq_one f (by simpa using h)

end General

variable {k : Type u} [Field k]

section Representations

variable {G H H' : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- Fixed vectors of a restriction only depend on the range of the restricting map. -/
theorem isFixedVector_restrict_of_range_le (ρ : MatrixRepresentation G n)
    (i : H ⟶ G) (j : H' ⟶ G)
    (h : SubgroupFunctor.range i ≤ SubgroupFunctor.range j) (v : n → k)
    (hv : (ρ.restrict j).IsFixedVector v) : (ρ.restrict i).IsFixedVector v := by
  intro T x
  have hx : x ≫ i.hom.hom ∈ (SubgroupFunctor.range j).carrier T :=
    h T ((SubgroupFunctor.mem_range (f := i) (x := x ≫ i.hom.hom)).mpr ⟨x, rfl⟩)
  obtain ⟨y, hy⟩ := (SubgroupFunctor.mem_range (f := j) (x := x ≫ i.hom.hom)).mp hx
  have h1 := hv T y
  rw [MatrixRepresentation.pointMatrix_restrict] at h1
  rw [MatrixRepresentation.pointMatrix_restrict, ← hy]
  exact h1

variable {Q : GroupScheme (Spec (CommRingCat.of k))}

/-- Per-representation form of `isUnipotent_of_kernel_of_quotient`: a representation whose
restriction to the kernel of an fpqc quotient map onto a unipotent group has a nonzero fixed
vector has a nonzero fixed vector itself. -/
theorem exists_fixedVector_of_kernel_of_quotient (q : G ⟶ Q)
    [IsAffineHom G.X.hom] [IsAffineHom (kernel q).X.hom]
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [QuasiCompact q.hom.hom.left]
    (ρ : MatrixRepresentation G n)
    (hK : ∃ v : n → k, v ≠ 0 ∧ (ρ.restrict (kernelι q)).IsFixedVector v)
    (hQ : IsUnipotent Q) : ∃ v : n → k, v ≠ 0 ∧ ρ.IsFixedVector v := by
  classical
  obtain ⟨v, hv, hfix⟩ := hK
  let W := (ρ.restrict (kernelι q)).fixedSubmodule
  let w : W := ⟨v, hfix⟩
  have hw : w ≠ 0 := fun h => hv (congrArg Subtype.val h)
  have hd : 0 < Module.finrank k W :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨w, hw⟩
  let : Nonempty (Fin (Module.finrank k W)) := ⟨⟨0, hd⟩⟩
  obtain ⟨B, C, hCB, hcols, hproj⟩ := MatrixRepresentation.exists_fixed_coordinates W
  have hN : (SubgroupFunctor.range (kernelι q)).IsNormal := by
    intro T g x _ hx
    apply (mem_range_kernelι_iff q _).mpr
    rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp,
      (mem_range_kernelι_iff q x).mp hx]
    simp
  have hGa : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hKa : IsAffine (kernel q).X.left := isAffine_of_isAffineHom (kernel q).X.hom
  obtain ⟨A, ⟨jG⟩⟩ := (essImage_algSpec (G := G.X)).mpr hGa
  obtain ⟨D, ⟨jK⟩⟩ := (essImage_algSpec (G := (kernel q).X)).mpr hKa
  have hs : ρ.IsStableCoordinates B C :=
    ρ.isStableCoordinates_of_affine_model jG B C
      (ρ.normal_fixed_coordinates_affine (kernelι q) hN jK B C hcols hproj
        A.unop jG.hom)
  let r := ρ.restrictCoordinates B C hCB hs
  let d := ρ.quotientFixedCoordinates q B C hCB hs hcols
  obtain ⟨z, hz, hdz⟩ := hQ (Fin (Module.finrank k W)) d
  have hrz : r.IsFixedVector z := by
    have h := (MatrixRepresentation.isFixedVector_restrict_iff d q z).2 hdz
    change MatrixRepresentation.IsFixedVector (q ≫ d) z at h
    have hfac : q ≫ d = r := ρ.quotientFixedCoordinates_fac q B C hCB hs hcols
    rwa [hfac] at h
  refine ⟨B *ᵥ z, ?_, ρ.isFixedVector_mulVec_restrictCoordinates B C hCB hs hrz⟩
  intro hbz
  apply hz
  exact MatrixRepresentation.coordinateInclusion_injective B C hCB
    (hbz.trans (Matrix.mulVec_zero B).symm)

end Representations

section Structural

variable {H G : GroupScheme (Spec (CommRingCat.of k))}

/-- A closed subgroup of an affine group scheme is affine. -/
theorem isAffineHom_of_isClosedSubgroup (i : H ⟶ G) (hi : IsClosedSubgroup i)
    [IsAffineHom G.X.hom] : IsAffineHom H.X.hom := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have h : IsAffineHom (i.hom.hom.left ≫ G.X.hom) := inferInstance
  rwa [Over.w i.hom.hom] at h

/-- A closed subgroup of a group scheme locally of finite type is locally of finite type. -/
theorem locallyOfFiniteType_of_isClosedSubgroup (i : H ⟶ G) (hi : IsClosedSubgroup i)
    [LocallyOfFiniteType G.X.hom] : LocallyOfFiniteType H.X.hom := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have h : LocallyOfFiniteType (i.hom.hom.left ≫ G.X.hom) := inferInstance
  rwa [Over.w i.hom.hom] at h

/-- Kernels of homomorphisms to affine group schemes are closed subgroups. -/
theorem isClosedSubgroup_kernelι {U : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom U.X.hom] (f : G ⟶ U) : IsClosedSubgroup (kernelι f) :=
  kernelι_isClosedImmersion f

/-- The standard additive group is affine. -/
instance vectorGroup_isAffineHom :
    IsAffineHom (VectorGroup.groupScheme (CommRingCat.of k) 1).X.hom := by
  change IsAffineHom
    (Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin 1) k))))
  infer_instance

/-- The standard additive group is locally of finite type. -/
instance vectorGroup_locallyOfFiniteType :
    LocallyOfFiniteType (VectorGroup.groupScheme (CommRingCat.of k) 1).X.hom := by
  change LocallyOfFiniteType
    (Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin 1) k))))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-- Products of affine group schemes are affine. -/
theorem isAffineHom_tensor (V C : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom V.X.hom] [IsAffineHom C.X.hom] : IsAffineHom (V ⊗ C).X.hom := by
  change IsAffineHom (pullback.fst V.X.hom C.X.hom ≫ V.X.hom)
  have hfst : IsAffineHom (pullback.fst V.X.hom C.X.hom) :=
    MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ inferInstance
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-- Products of group schemes locally of finite type are locally of finite type. -/
theorem locallyOfFiniteType_tensor (V C : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType V.X.hom] [LocallyOfFiniteType C.X.hom] :
    LocallyOfFiniteType (V ⊗ C).X.hom := by
  change LocallyOfFiniteType (pullback.fst V.X.hom C.X.hom ≫ V.X.hom)
  have hfst : LocallyOfFiniteType (pullback.fst V.X.hom C.X.hom) :=
    MorphismProperty.pullback_fst (P := @LocallyOfFiniteType) _ _ inferInstance
  infer_instance

end Structural

section MinimalKernel

variable (G : GroupScheme (Spec (CommRingCat.of k)))

/-- The coordinate ideals of kernels of homomorphisms from `G` to affine unipotent groups
locally of finite type. -/
def unipotentKernelIdeals : Set (Ideal Γ(G.X.left, ⊤)) :=
  {I | ∃ (U : GroupScheme (Spec (CommRingCat.of k))) (_ : IsAffineHom U.X.hom)
      (_ : LocallyOfFiniteType U.X.hom) (f : G ⟶ U),
      IsUnipotent U ∧ BorelExistence.coordinateKernel (kernelι f) = I}

/-- Some homomorphism to an affine unipotent group of finite type has a kernel contained in
the kernel of every other such homomorphism. -/
theorem exists_minimal_unipotent_kernel [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] :
    ∃ (U : GroupScheme (Spec (CommRingCat.of k))) (_ : IsAffineHom U.X.hom)
      (_ : LocallyOfFiniteType U.X.hom) (f : G ⟶ U), IsUnipotent U ∧
      ∀ (V : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom V.X.hom]
        [LocallyOfFiniteType V.X.hom] (g : G ⟶ V), IsUnipotent V →
        SubgroupFunctor.range (kernelι f) ≤ SubgroupFunctor.range (kernelι g) := by
  have hnoeth := BorelExistence.isNoetherianRing_globalSections G
  have hne : (unipotentKernelIdeals G).Nonempty :=
    ⟨_, VectorGroup.groupScheme (CommRingCat.of k) 1, inferInstance, inferInstance, 0,
      VectorGroup.isUnipotent k 1, rfl⟩
  obtain ⟨I, ⟨U, hUa, hUl, f, hU, rfl⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr hnoeth (unipotentKernelIdeals G) hne
  refine ⟨U, hUa, hUl, f, hU, ?_⟩
  intro V _ _ g hV
  let : IsAffineHom (U ⊗ V).X.hom := isAffineHom_tensor U V
  let : LocallyOfFiniteType (U ⊗ V).X.hom := locallyOfFiniteType_tensor U V
  let p : G ⟶ U ⊗ V := lift f g
  have hpf : p ≫ fst U V = f := lift_fst f g
  have hpg : p ≫ snd U V = g := lift_snd f g
  have hle : SubgroupFunctor.range (kernelι p) ≤ SubgroupFunctor.range (kernelι f) :=
    AffineQuotient.range_kernelι_le_of_comp_eq hpf
  have hle' : SubgroupFunctor.range (kernelι p) ≤ SubgroupFunctor.range (kernelι g) :=
    AffineQuotient.range_kernelι_le_of_comp_eq hpg
  let φ : kernel p ⟶ kernel f := SubgroupFunctor.factorOfRangeLE hle
  have hφ : φ ≫ kernelι f = kernelι p := SubgroupFunctor.factorOfRangeLE_comp hle
  have hcl := BorelExistence.coordinateKernel_le (kernelι p) (kernelι f) φ hφ
  have hmem : BorelExistence.coordinateKernel (kernelι p) ∈ unipotentKernelIdeals G :=
    ⟨U ⊗ V, inferInstance, inferInstance, p,
      SubgroupProductOrbit.isUnipotent_tensor U V hU hV, rfl⟩
  have heq : BorelExistence.coordinateKernel (kernelι p) =
      BorelExistence.coordinateKernel (kernelι f) :=
    (eq_of_le_of_not_lt hcl (hmax _ hmem)).symm
  have : IsIso φ := BorelExistence.isIso_of_coordinateKernel_eq (kernelι p) (kernelι f) φ
    (isClosedSubgroup_kernelι p) (isClosedSubgroup_kernelι f) hφ heq
  calc SubgroupFunctor.range (kernelι f)
      = SubgroupFunctor.range ((asIso φ).hom ≫ kernelι f) :=
        (SubgroupFunctor.range_iso_comp (asIso φ) (kernelι f)).symm
    _ = SubgroupFunctor.range (kernelι p) := by rw [asIso_hom, hφ]
    _ ≤ SubgroupFunctor.range (kernelι g) := hle'

end MinimalKernel

section KernelLemmas

variable {S : Scheme.{u}} {A B C : GroupScheme S}

/-- Ranges of commutative groups are normal. -/
theorem range_isNormal_of_comm [IsCommMonObj B.X] (i : A ⟶ B) :
    (SubgroupFunctor.range i).IsNormal := by
  intro T g x _ hx
  simpa only [mul_comm g x, mul_assoc, mul_inv_cancel, mul_one] using hx

/-- A homomorphism kills a subgroup contained in its kernel. -/
theorem comp_eq_zero_of_range_le {i : A ⟶ B} {q : B ⟶ C}
    (h : SubgroupFunctor.range i ≤ SubgroupFunctor.range (kernelι q)) : i ≫ q = 0 := by
  have hx : i.hom.hom ∈ (SubgroupFunctor.range i).carrier A.X :=
    SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩
  have h1 := (mem_range_kernelι_iff q _).mp (h _ hx)
  apply Grp.hom_ext
  rw [Grp.comp_hom_hom, h1]
  rfl

/-- The kernel of `g` lies in the kernel of every homomorphism killing it. -/
theorem range_kernelι_le_of_comp_eq_zero {g : A ⟶ B} {f : A ⟶ C}
    (h : kernelι g ≫ f = 0) :
    SubgroupFunctor.range (kernelι g) ≤ SubgroupFunctor.range (kernelι f) := by
  intro T x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  rw [mem_range_kernelι_iff, Category.assoc, ← Grp.comp_hom_hom, h]
  exact MonObj.comp_one y

end KernelLemmas

section MultiplicativePart

variable (G : GroupScheme (Spec (CommRingCat.of k)))

/-- Restriction preserves fixed vectors. -/
theorem isFixedVector_restrict {H : GroupScheme (Spec (CommRingCat.of k))}
    {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n) (q : H ⟶ G)
    (v : n → k) (h : ρ.IsFixedVector v) : (ρ.restrict q).IsFixedVector v := by
  intro T x
  rw [MatrixRepresentation.pointMatrix_restrict]
  exact h T (x ≫ q.hom.hom)

/-- If `f₀ : G ⟶ U₀` has the smallest kernel among homomorphisms to affine unipotent groups of
finite type, then its kernel is of multiplicative type (Milne 2017, proof of 16.13(a)). -/
theorem isMultiplicativeType_kernel_of_minimal [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] [IsCommMonObj G.X]
    {U₀ : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom U₀.X.hom]
    [LocallyOfFiniteType U₀.X.hom] (f₀ : G ⟶ U₀) (hU₀ : IsUnipotent U₀)
    (hmin : ∀ (V : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom V.X.hom]
      [LocallyOfFiniteType V.X.hom] (g : G ⟶ V), IsUnipotent V →
      SubgroupFunctor.range (kernelι f₀) ≤ SubgroupFunctor.range (kernelι g)) :
    IsMultiplicativeType (kernel f₀) := by
  have hs₀ : IsClosedSubgroup (kernelι f₀) := isClosedSubgroup_kernelι f₀
  have : IsAffineHom (kernel f₀).X.hom := isAffineHom_of_isClosedSubgroup _ hs₀
  have : LocallyOfFiniteType (kernel f₀).X.hom := locallyOfFiniteType_of_isClosedSubgroup _ hs₀
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨I₀, q₀, i₀, hI₀l, hI₀a, hi₀, -, hq₀⟩ := affineHomImage k G U₀ f₀
  have hI₀ : IsUnipotent I₀ := unipotentClosedSubgroup k U₀ I₀ i₀ hi₀ hU₀
  have : IsAffine I₀.X.left := isAffine_of_isAffineHom I₀.X.hom
  have : IsAffineHom (kernel q₀).X.hom :=
    isAffineHom_of_isClosedSubgroup _ (isClosedSubgroup_kernelι q₀)
  have : Flat q₀.hom.hom.left := hq₀.1
  have : Surjective q₀.hom.hom.left := hq₀.2.1
  suffices hzero : ∀ g : kernel f₀ ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1, g = 0 by
    have hcriterion :
        (IsCommMonObj (kernel f₀).X ∧
          Subsingleton (kernel f₀ ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1)) ↔
        IsMultiplicativeType (kernel f₀) :=
      (multiplicativeTypeCharacterization k (kernel f₀) (SeparableClosure k)).out 2 1
    exact hcriterion.mp ⟨inferInstance, ⟨fun g g' => by rw [hzero g, hzero g']⟩⟩
  intro g
  let n : kernel g ⟶ G := kernelι g ≫ kernelι f₀
  have hn : IsClosedSubgroup n := by
    have : IsClosedImmersion (kernelι g).hom.hom.left := isClosedSubgroup_kernelι g
    have : IsClosedImmersion (kernelι f₀).hom.hom.left := hs₀
    change IsClosedImmersion ((kernelι g).hom.hom.left ≫ (kernelι f₀).hom.hom.left)
    infer_instance
  obtain ⟨QN, qN, hQNl, hQNa, hqN⟩ :=
    affineNormalSubgroupQuotient k G (kernel g) n hn (range_isNormal_of_comm n)
  have : Flat qN.hom.hom.left := hqN.1
  have : Surjective qN.hom.hom.left := hqN.2.1
  have : Epi qN.hom.hom.left := Flat.epi_of_flat_of_surjective _
  have hnq : n ≫ qN = 0 := comp_eq_zero_of_range_le hqN.2.2.2.ge
  -- the image of `g` is a closed subgroup of `𝔾ₐ`, hence unipotent
  obtain ⟨J, qg, ig, hJl, hJa, hig, -, hqg⟩ :=
    affineHomImage k (kernel f₀) (VectorGroup.groupScheme (CommRingCat.of k) 1) g
  have hJ : IsUnipotent J :=
    unipotentClosedSubgroup k _ J ig hig (VectorGroup.isUnipotent k 1)
  have : Flat qg.hom.hom.left := hqg.1
  have : Surjective qg.hom.hom.left := hqg.2.1
  have : LocallyOfFinitePresentation qg.hom.hom.left := hqg.2.2.1
  have hQN : IsUnipotent QN := by
    intro m _ _ _ ρ
    have hk : kernelι qg ≫ (kernelι f₀ ≫ qN ≫ ρ) = 0 := by
      apply AffineQuotient.kernelι_comp_eq_zero
      rw [hqg.2.2.2]
      apply range_kernelι_le_of_comp_eq_zero
      rw [← Category.assoc, ← Category.assoc]
      change (n ≫ qN) ≫ ρ = 0
      rw [hnq, zero_comp]
    let ρJ : MatrixRepresentation J m := FppfHomDescent.hom qg (kernelι f₀ ≫ qN ≫ ρ) hk
    obtain ⟨v, hv, hfixJ⟩ := hJ m ρJ
    have hfix₀ : ((ρ.restrict qN).restrict (kernelι f₀)).IsFixedVector v := by
      have h := isFixedVector_restrict J ρJ qg v hfixJ
      have hfac : ρJ.restrict qg = (ρ.restrict qN).restrict (kernelι f₀) :=
        FppfHomDescent.fac qg (kernelι f₀ ≫ qN ≫ ρ) hk
      rwa [hfac] at h
    obtain ⟨w, hw, hfix⟩ := exists_fixedVector_of_kernel_of_quotient q₀ (ρ.restrict qN)
      ⟨v, hv, isFixedVector_restrict_of_range_le (ρ.restrict qN) (kernelι q₀) (kernelι f₀)
        hq₀.2.2.2.le v hfix₀⟩ hI₀
    exact ⟨w, hw, (MatrixRepresentation.isFixedVector_restrict_iff ρ qN w).mp hfix⟩
  have hle : SubgroupFunctor.range (kernelι f₀) ≤ SubgroupFunctor.range n :=
    (hmin QN qN hQN).trans hqN.2.2.2.le
  obtain ⟨y, hy⟩ := (SubgroupFunctor.mem_range (f := n)).mp
    (hle _ ((SubgroupFunctor.mem_range (f := kernelι f₀)).mpr ⟨𝟙 _, Category.id_comp _⟩))
  have hy' : y ≫ (kernelι g).hom.hom = 𝟙 _ := by
    apply (cancel_mono (kernelι f₀).hom.hom).mp
    rw [Category.assoc, Category.id_comp]
    exact hy
  have hg : (kernelι g).hom.hom ≫ g.hom.hom = 1 :=
    (mem_range_kernelι_iff g _).mp
      ((SubgroupFunctor.mem_range (f := kernelι g)).mpr ⟨𝟙 _, Category.id_comp _⟩)
  apply eq_zero_of_hom_eq_one
  rw [← Category.id_comp g.hom.hom, ← hy', Category.assoc, hg]
  exact MonObj.comp_one y

/-- A homomorphism to an affine unipotent group kills every subgroup of multiplicative type
(Milne 2017, 14.18). -/
theorem range_le_kernel_of_isMultiplicativeType {U₀ : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom U₀.X.hom] (f₀ : G ⟶ U₀) (hU₀ : IsUnipotent U₀)
    {H : GroupScheme (Spec (CommRingCat.of k))} (h : H ⟶ G) (hH : IsMultiplicativeType H) :
    SubgroupFunctor.range h ≤ SubgroupFunctor.range (kernelι f₀) := by
  have h0 : h ≫ f₀ = 0 := hH.hom_eq_zero_of_isUnipotent hU₀ (h ≫ f₀)
  intro T x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  rw [mem_range_kernelι_iff, Category.assoc, ← Grp.comp_hom_hom, h0]
  exact MonObj.comp_one y

/-- Milne 2017, Theorem 16.13(a), without the characteristic clause: a commutative affine
algebraic group has a largest closed subgroup of multiplicative type, and the fppf quotient by
it is an affine unipotent group of finite type. -/
theorem exists_multiplicativePart [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]
    [IsCommMonObj G.X] :
    ∃ (S Q : GroupScheme (Spec (CommRingCat.of k))) (s : S ⟶ G) (q : G ⟶ Q),
      IsClosedSubgroup s ∧ IsMultiplicativeType S ∧
        (∀ (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ G),
          IsClosedSubgroup h → IsMultiplicativeType H →
            SubgroupFunctor.range h ≤ SubgroupFunctor.range s) ∧
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range s) q ∧ IsUnipotent Q ∧
        LocallyOfFiniteType Q.X.hom ∧ IsAffineHom Q.X.hom := by
  obtain ⟨U₀, hU₀a, hU₀l, f₀, hU₀, hmin⟩ := exists_minimal_unipotent_kernel G
  obtain ⟨I₀, q₀, i₀, hI₀l, hI₀a, hi₀, -, hq₀⟩ := affineHomImage k G U₀ f₀
  refine ⟨kernel f₀, I₀, kernelι f₀, q₀, isClosedSubgroup_kernelι f₀,
    isMultiplicativeType_kernel_of_minimal G f₀ hU₀ hmin,
    fun H h _ hH => range_le_kernel_of_isMultiplicativeType G f₀ hU₀ h hH, ?_,
    unipotentClosedSubgroup k U₀ I₀ i₀ hi₀ hU₀, hI₀l, hI₀a⟩
  exact hq₀

end MultiplicativePart

end CommutativeDecomposition

end Langlands.GroupScheme
