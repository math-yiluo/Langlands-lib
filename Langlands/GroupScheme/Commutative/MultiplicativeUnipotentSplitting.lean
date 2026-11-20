import Langlands.GroupScheme.Commutative.MultiplicativeUnipotentUniqueness
import Langlands.GroupScheme.Torus.MultiplicativeTypeFieldExtensionProof
import Langlands.GroupScheme.Unipotent.BaseChange
import Langlands.GroupScheme.Unipotent.HopfFixed
import Langlands.GroupScheme.Descent.GaloisHom
import Langlands.GroupScheme.CommutativeSplitProduct
import Langlands.GroupScheme.Reductive.UnipotentQuotient
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra

/-! # Splitting off the multiplicative part over a perfect field (Milne 16.13(b))

Let `G` be a commutative affine algebraic group over a perfect field `k`, `s : S ⟶ G` a closed
subgroup of multiplicative type and `q : G ⟶ Q` an fppf quotient map with kernel `S` and
unipotent target. Then `s` has a retraction homomorphism `G ⟶ S`. Over an algebraic closure the
retraction comes from the coordinate Hopf algebra: it is graded by the characters of `S`, and
each graded piece has a unique group-like element. The retraction is unique, hence Galois
compatible, and descends to `k`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct Coalgebra
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RelativeRoot

namespace CommutativeDecomposition

section Hopf

variable {K : Type u} [Field K]

/-- In a unipotent coordinate bialgebra over a field, the only group-like element is `1`. -/
theorem eq_one_of_isGroupLikeElem {B : Type u} [Ring B] [Bialgebra K B]
    (hB : Unipotent.OneMemStable K B) {b : B} (hb : IsGroupLikeElem K b) : b = 1 := by
  have hstab : ∀ (f : Module.Dual K B) (v : B), v ∈ K ∙ b →
      AffineLinearEmbedding.rightAct f v ∈ K ∙ b := by
    intro f v hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul, AffineLinearEmbedding.rightAct_apply, hb.comul_eq_tmul_self,
      LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self b))
  have hne : (K ∙ b) ≠ ⊥ := by
    rw [Ne, Submodule.span_singleton_eq_bot]
    exact hb.ne_zero
  have h1 := hB (K ∙ b) inferInstance hstab hne
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h1
  have hc1 : c = 1 := by
    have := congrArg (counit (R := K)) hc
    rwa [map_smul, hb.counit_eq_one, Bialgebra.counit_one, smul_eq_mul, mul_one] at this
  rw [← hc, hc1, one_smul]

variable {N : Type u} [AddCommGroup N] {A B : Type u} [CommRing A] [HopfAlgebra K A]
  [CommRing B] [HopfAlgebra K B]

/-- Let `φ : B → A` be injective with image the degree-zero part of the grading of `A` defined
by `π : A → K[N]`. If `B` is unipotent, the only group-like element of degree zero is `1`. -/
theorem eq_one_of_mem_grade_zero (φ : B →ₐc[K] A) (π : A →ₐc[K] AddMonoidAlgebra K N)
    (hφ : Function.Injective φ)
    (hinv : ∀ a ∈ GroupAlgebraCoaction.grade π 0, ∃ b, φ b = a)
    (hB : Unipotent.OneMemStable K B) {g : A} (hg : IsGroupLikeElem K g)
    (hg0 : g ∈ GroupAlgebraCoaction.grade π 0) : g = 1 := by
  obtain ⟨b, rfl⟩ := hinv g hg0
  have hb : IsGroupLikeElem K b :=
    { counit_eq_one := by
        rw [← CoalgHomClass.counit_comp_apply φ b]
        exact hg.counit_eq_one
      comul_eq_tmul_self := by
        apply TensorProduct.map_injective_of_flat_flat (φ : B →ₗ[K] A) (φ : B →ₗ[K] A) hφ hφ
        rw [CoalgHomClass.map_comp_comul_apply, hg.comul_eq_tmul_self, TensorProduct.map_tmul]
        rfl }
  rw [eq_one_of_isGroupLikeElem hB hb, map_one]

/-- Under the hypotheses of `eq_one_of_mem_grade_zero`, the degree of group-like elements is
injective. -/
theorem degree_injective (φ : B →ₐc[K] A) (π : A →ₐc[K] AddMonoidAlgebra K N)
    (hφ : Function.Injective φ)
    (hinv : ∀ a ∈ GroupAlgebraCoaction.grade π 0, ∃ b, φ b = a)
    (hB : Unipotent.OneMemStable K B) :
    Function.Injective (CentralDiagonalizableExtensionHopf.degree π) := by
  rw [injective_iff_map_eq_zero]
  intro g hg
  have hg0 : (g.toMul : A) ∈ GroupAlgebraCoaction.grade π 0 :=
    hg ▸ CentralDiagonalizableExtensionHopf.mem_grade_degree g
  have h1 := eq_one_of_mem_grade_zero φ π hφ hinv hB g.toMul.isGroupLikeElem_val hg0
  apply Additive.toMul.injective
  apply GroupLike.val_injective
  rw [h1]
  rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward false in
/-- If `Spec π` is a closed subgroup of `Spec A` with `π : A → K[N]`, and `Spec φ` is an fppf
quotient map with kernel `Spec π`, then the degree-zero part of the grading of `A` defined by `π`
lies in the image of `φ`. (This is the `invariants` field of
`CentralExtensionHopfSpec.isExtension_diagonalizable`, whose proof is repeated for an arbitrary
`B`.) -/
theorem exists_eq_of_mem_grade_zero {N : Type u} [AddCommGroup N]
    {A B : CommHopfAlgCat.{u} (CommRingCat.of K)}
    (φ : B ⟶ A) (π : A ⟶ Diagonalizable.hopfAlgebra (CommRingCat.of K) N)
    (hz : IsClosedSubgroup ((hopfSpec (CommRingCat.of K)).map π.op))
    (hq : IsFppfQuotient (SubgroupFunctor.range ((hopfSpec (CommRingCat.of K)).map π.op))
      ((hopfSpec (CommRingCat.of K)).map φ.op)) :
    ∀ a ∈ GroupAlgebraCoaction.grade π.hom 0, ∃ b, φ.hom b = a := by
  intro a ha
  have : IsClosedImmersion ((hopfSpec (CommRingCat.of K)).map π.op).hom.hom.left := hz
  refine CentralExtensionHopfSpec.exists_eq_of_lTensor_comul_eq φ π
    (Over.mono_of_mono_left _) hq a ?_
  rw [GroupAlgebraCoaction.mem_grade_iff, GroupAlgebraCoaction.coaction_apply] at ha
  rw [← (AddMonoidAlgebra.scalarTensorEquiv K A).symm_apply_apply
    ((π.hom : A →ₗ[K] AddMonoidAlgebra K N).lTensor A (Coalgebra.comul a)), ha,
    AddMonoidAlgebra.scalarTensorEquiv_symm_single, ← AddMonoidAlgebra.one_def]

/-- Over an algebraically closed field, for a cocommutative `A` and surjective `π`, the degree
of group-like elements is surjective. -/
theorem degree_surjective [IsAlgClosed K] [Coalgebra.IsCocomm K A]
    (π : A →ₐc[K] AddMonoidAlgebra K N) (hπ : Function.Surjective π) :
    Function.Surjective (CentralDiagonalizableExtensionHopf.degree π) := by
  intro n
  obtain ⟨g, hg, hgn⟩ := GroupAlgebraCoaction.exists_isGroupLikeElem_mem_grade π
    (GroupAlgebraCoaction.grade_ne_bot_of_surjective π hπ n)
  exact ⟨Additive.ofMul ⟨g, hg⟩, CentralDiagonalizableExtensionHopf.degree_eq_of_mem_grade hgn⟩

/-- The bialgebra map `K[N] → A` sending `Xⁿ` to the group-like element `e n`. -/
def sectionHom (e : N →+ Additive (GroupLike K A)) : AddMonoidAlgebra K N →ₐc[K] A :=
  (MonoidAlgebra.liftGroupLikeBialgHom (R := K) (A := A)).comp
    (((MonoidAlgebra.toAdditiveBialgEquiv K K (GroupLike K A)).symm :
        AddMonoidAlgebra K (Additive (GroupLike K A)) →ₐc[K] MonoidAlgebra K (GroupLike K A)).comp
      (AddMonoidAlgebra.mapDomainBialgHom K e))

theorem sectionHom_single (e : N →+ Additive (GroupLike K A)) (n : N) :
    sectionHom e (AddMonoidAlgebra.single n 1) = ((e n).toMul : A) := by
  have h : ∀ g : GroupLike K A, (MonoidAlgebra.toAdditiveBialgEquiv K K (GroupLike K A)).symm
      (AddMonoidAlgebra.single (Additive.ofMul g) 1) = MonoidAlgebra.single g 1 := by
    intro g
    rw [← MonoidAlgebra.toAdditiveBialgEquiv_single (R := K) (A := K) g (1 : K)]
    exact BialgEquiv.symm_apply_apply _ _
  simp only [sectionHom, BialgHom.comp_apply, AddMonoidAlgebra.mapDomainBialgHom_single]
  erw [h (e n).toMul]
  simp [MonoidAlgebra.liftGroupLikeBialgHom]

/-- If `π` sends the group-like element `e n` to `Xⁿ` for all `n`, then `sectionHom e` is a
section of `π`. -/
theorem comp_sectionHom (π : A →ₐc[K] AddMonoidAlgebra K N) (e : N →+ Additive (GroupLike K A))
    (he : ∀ n, CentralDiagonalizableExtensionHopf.degree π (e n) = n) :
    π.comp (sectionHom e) = BialgHom.id K (AddMonoidAlgebra K N) := by
  apply BialgHom.coe_toAlgHom_injective
  refine AddMonoidAlgebra.algHom_ext (fun n => ?_) (Subsingleton.elim _ _)
  change π (sectionHom e (AddMonoidAlgebra.single n 1)) = AddMonoidAlgebra.single n 1
  rw [sectionHom_single, CentralDiagonalizableExtensionHopf.map_eq_single_degree, he]

/-- A bialgebra section of `π` is determined by the degrees, when these are injective. -/
theorem eq_of_comp_eq_id (π : A →ₐc[K] AddMonoidAlgebra K N)
    (hinj : Function.Injective (CentralDiagonalizableExtensionHopf.degree π))
    (ψ ψ' : AddMonoidAlgebra K N →ₐc[K] A)
    (hψ : π.comp ψ = BialgHom.id K _) (hψ' : π.comp ψ' = BialgHom.id K _) : ψ = ψ' := by
  apply BialgHom.coe_toAlgHom_injective
  refine AddMonoidAlgebra.algHom_ext (fun n => ?_) (Subsingleton.elim _ _)
  have key : ∀ χ : AddMonoidAlgebra K N →ₐc[K] A, π.comp χ = BialgHom.id K _ →
      ∃ g : Additive (GroupLike K A), CentralDiagonalizableExtensionHopf.degree π g = n ∧
        (g.toMul : A) = χ (AddMonoidAlgebra.single n 1) := by
    intro χ hχ
    let g : Additive (GroupLike K A) :=
      Additive.ofMul ⟨χ (AddMonoidAlgebra.single n 1),
        (AddMonoidAlgebra.isGroupLikeElem_single_one n).map χ⟩
    refine ⟨g, ?_, rfl⟩
    apply CentralDiagonalizableExtensionHopf.degree_eq_of_mem_grade
    apply CentralDiagonalizableExtensionHopf.mem_grade_of_isGroupLikeElem
      g.toMul.isGroupLikeElem_val
    change (π.comp χ) (AddMonoidAlgebra.single n 1) = _
    rw [hχ]
    rfl
  obtain ⟨g, hg, hgψ⟩ := key ψ hψ
  obtain ⟨g', hg', hgψ'⟩ := key ψ' hψ'
  have : g = g' := hinj (hg.trans hg'.symm)
  change ψ (AddMonoidAlgebra.single n 1) = ψ' (AddMonoidAlgebra.single n 1)
  rw [← hgψ, ← hgψ', this]

end Hopf

section AlgClosed

variable {K : Type u} [Field K]

/-- The coordinate Hopf algebra of a unipotent affine group over a field has the property
`OneMemStable`. -/
theorem oneMemStable_hopfAlgebra (T : GroupScheme (Spec (CommRingCat.of K)))
    [IsAffine T.X.left] (hT : IsUnipotent T) :
    Unipotent.OneMemStable K (AffineCoordinates.hopfAlgebra T) :=
  Unipotent.oneMemStable_of_isUnipotent_cogroup (AffineCoordinates.coordinateCogroup T)
    (IsUnipotent.of_iso (AffineCoordinates.coordinateCogroupIso T) hT)

set_option maxHeartbeats 1000000 in
/-- Over an algebraically closed field, let `E` be a commutative affine group scheme, `z : Z ⟶ E`
a closed subgroup with `Z ≅ D(N)` diagonalizable, and `p : E ⟶ T` an fppf quotient map with
kernel `Z` and affine unipotent target. Then `z` has exactly one retraction homomorphism. -/
theorem exists_unique_retraction_of_isAlgClosed [IsAlgClosed K]
    {E Z T : GroupScheme (Spec (CommRingCat.of K))}
    [IsAffine E.X.left] [IsCommMonObj E.X] [IsAffine T.X.left]
    {N : Type u} [AddCommGroup N]
    (eZ0 : Z ≅ (Diagonalizable.groupScheme (CommRingCat.of K) N).toGrp)
    (z : Z ⟶ E) (hz : IsClosedSubgroup z) (p : E ⟶ T)
    (hq : IsFppfQuotient (SubgroupFunctor.range z) p) (hT : IsUnipotent T) :
    ∃ r : E ⟶ Z, z ≫ r = 𝟙 Z ∧ ∀ r' : E ⟶ Z, z ≫ r' = 𝟙 Z → r' = r := by
  classical
  let R := CommRingCat.of K
  let A := AffineCoordinates.hopfAlgebra E
  let eE := AffineCoordinates.hopfSpecIso E
  let B := AffineCoordinates.hopfAlgebra T
  let eT := AffineCoordinates.hopfSpecIso T
  let eZ : (hopfSpec R).obj (op (Diagonalizable.hopfAlgebra R N)) ≅ Z :=
    Diagonalizable.hopfSpecIso R N ≪≫ eZ0.symm
  let π : A ⟶ Diagonalizable.hopfAlgebra R N :=
    (hopfSpec.fullyFaithful.preimage (eZ.hom ≫ z ≫ eE.symm.hom)).unop
  let φ : B ⟶ A :=
    (hopfSpec.fullyFaithful.preimage (eE.symm.inv ≫ p ≫ eT.symm.hom)).unop
  have hπ : (hopfSpec R).map π.op = eZ.hom ≫ z ≫ eE.symm.hom :=
    hopfSpec.fullyFaithful.map_preimage _
  have hφ : (hopfSpec R).map φ.op = eE.symm.inv ≫ p ≫ eT.symm.hom :=
    hopfSpec.fullyFaithful.map_preimage _
  have hz' : IsClosedSubgroup ((hopfSpec R).map π.op) := by
    rw [hπ]
    exact IsClosedSubgroup.iso_comp eZ (hz.comp_iso eE.symm)
  have hq' : IsFppfQuotient (SubgroupFunctor.range ((hopfSpec R).map π.op))
      ((hopfSpec R).map φ.op) := by
    rw [hπ, hφ, SubgroupFunctor.range_iso_comp, SubgroupFunctor.range_comp_iso,
      ← Category.assoc]
    exact (hq.comapIso eE.symm).comp_iso eT.symm
  have hπs : Function.Surjective π.hom :=
    CentralExtensionHopfSpec.surjective_of_isClosedSubgroup π hz'
  have hφi : Function.Injective φ.hom :=
    (CentralExtensionHopfSpec.faithfullyFlat_of_isFppfQuotient φ hq').injective
  have hinv := exists_eq_of_mem_grade_zero φ π hz' hq'
  have hB : Unipotent.OneMemStable K B := oneMemStable_hopfAlgebra T hT
  have : Coalgebra.IsCocomm K A := AffineCoordinates.hopfAlgebra_isCocomm E
  have hinj := degree_injective φ.hom π.hom hφi hinv hB
  have hsurj := degree_surjective π.hom hπs
  let e : N ≃+ Additive (GroupLike K A) :=
    (AddEquiv.ofBijective (CentralDiagonalizableExtensionHopf.degree π.hom) ⟨hinj, hsurj⟩).symm
  have he : ∀ n, CentralDiagonalizableExtensionHopf.degree π.hom (e n) = n := fun n =>
    (AddEquiv.ofBijective _ ⟨hinj, hsurj⟩).apply_symm_apply n
  let ψ : Diagonalizable.hopfAlgebra R N ⟶ A :=
    CommHopfAlgCat.ofHom (sectionHom e.toAddMonoidHom)
  have hψπ : π.hom.comp ψ.hom = BialgHom.id K _ := comp_sectionHom π.hom e.toAddMonoidHom he
  have hzπ : z ≫ eE.inv = eZ.inv ≫ (hopfSpec R).map π.op := by
    rw [hπ]
    simp
  refine ⟨eE.inv ≫ (hopfSpec R).map ψ.op ≫ eZ.hom, ?_, ?_⟩
  · have hc : ψ ≫ π = 𝟙 _ := CommHopfAlgCat.hom_ext hψπ
    rw [← Category.assoc, hzπ, Category.assoc, ← Functor.map_comp_assoc, ← op_comp, hc]
    simp
  · intro r' hr'
    let χ : Diagonalizable.hopfAlgebra R N ⟶ A :=
      (hopfSpec.fullyFaithful.preimage (eE.hom ≫ r' ≫ eZ.inv)).unop
    have hχ : (hopfSpec R).map χ.op = eE.hom ≫ r' ≫ eZ.inv :=
      hopfSpec.fullyFaithful.map_preimage _
    have hc : χ ≫ π = 𝟙 _ := by
      apply Quiver.Hom.op_inj
      apply hopfSpec.fullyFaithful.map_injective
      rw [op_comp, Functor.map_comp, hχ, hπ]
      simp [reassoc_of% hr']
    have hχψ : χ = ψ := CommHopfAlgCat.hom_ext
      (eq_of_comp_eq_id π.hom hinj χ.hom ψ.hom (congrArg CommHopfAlgCat.Hom.hom hc) hψπ)
    rw [← hχψ, hχ]
    simp

end AlgClosed

section Perfect

variable {k : Type u} [Field k]

/-- **Retraction onto the multiplicative part over a perfect field.** Let `G` be a commutative
affine group over a perfect field, `s : S ⟶ G` a closed subgroup of multiplicative type and
`q : G ⟶ Q` an fppf quotient map with kernel `S` and unipotent affine target. Then `s` has a
retraction homomorphism. -/
theorem exists_retraction_of_perfectField [PerfectField k]
    {G S Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsCommMonObj G.X] [IsAffineHom Q.X.hom]
    (s : S ⟶ G) (hs : IsClosedSubgroup s) (hS : IsMultiplicativeType S)
    (q : G ⟶ Q) (hq : IsFppfQuotient (SubgroupFunctor.range s) q) (hQ : IsUnipotent Q) :
    ∃ r : G ⟶ S, s ≫ r = 𝟙 S := by
  let L := AlgebraicClosure k
  have : IsGalois k L := {}
  have : IsAffineHom S.X.hom := hS.isAffineHom
  let b := algebraBaseMap k L
  let F := GroupScheme.baseChange b
  have hSL : IsMultiplicativeType (F.obj S) :=
    MultiplicativeTypeSplitting.isMultiplicativeType_baseChange_of_isAlgebraic k L S hS
  obtain ⟨N, hN, -, ⟨eS⟩⟩ :=
    MultiplicativeTypeSplitting.isFGDiagonalizable_of_isSepClosed (F.obj S) hSL
  have hs' : IsClosedSubgroup (F.map s) := hs.baseChange b
  have hq' : IsFppfQuotient (SubgroupFunctor.range (F.map s)) (F.map q) := by
    rw [SubgroupFunctor.range_baseChangeHom]
    exact hq.baseChange b
  have hQ' : IsUnipotent (F.obj Q) := hQ.baseChange (K := L)
  have : IsAffineHom (F.obj G).X.hom :=
    MorphismProperty.pullback_snd _ _ (inferInstance : IsAffineHom G.X.hom)
  have : IsAffineHom (F.obj Q).X.hom :=
    MorphismProperty.pullback_snd _ _ (inferInstance : IsAffineHom Q.X.hom)
  have : IsAffine (F.obj G).X.left := isAffine_of_isAffineHom (F.obj G).X.hom
  have : IsAffine (F.obj Q).X.left := isAffine_of_isAffineHom (F.obj Q).X.hom
  have : IsCommMonObj (F.obj G).X :=
    Functor.isCommMonObj_obj (F := Over.pullback b) (M := G.X)
  obtain ⟨r, hr, hru⟩ :=
    exists_unique_retraction_of_isAlgClosed eS (F.map s) hs' (F.map q) hq' hQ'
  have hf : ∀ σ : L ≃ₐ[k] L,
      (GroupScheme.baseChange (galoisBaseMap k L σ)).map r ≫
          (descentBaseChangeIso b (galoisBaseMap k L σ) (galoisBaseMap_over k L σ) S).hom =
        (descentBaseChangeIso b (galoisBaseMap k L σ) (galoisBaseMap_over k L σ) G).hom ≫ r := by
    intro σ
    let D := descentBaseChangeIso b (galoisBaseMap k L σ) (galoisBaseMap_over k L σ)
    let Fσ := GroupScheme.baseChange (galoisBaseMap k L σ)
    have hn := descentBaseChangeIso_naturality b (galoisBaseMap k L σ)
      (galoisBaseMap_over k L σ) s
    have hn' : F.map s ≫ (D G).inv = (D S).inv ≫ Fσ.map (F.map s) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact hn.symm ▸ (Iso.inv_hom_id_assoc (D S) (F.map s)).symm
    have hα := hru ((D G).inv ≫ Fσ.map r ≫ (D S).hom) (by
      rw [reassoc_of% hn', ← Fσ.map_comp_assoc, hr, Fσ.map_id, Category.id_comp,
        Iso.inv_hom_id])
    exact (Iso.inv_comp_eq (D G)).mp hα
  refine ⟨Descent.GaloisHom.hom r hf, ?_⟩
  have : Surjective b := (fieldExtension_fpqc k L).1
  have : Flat b := (fieldExtension_fpqc k L).2.1
  have : QuasiCompact b := (fieldExtension_fpqc k L).2.2
  apply Grp.hom_ext
  apply (Over.pullback b).map_injective
  change (F.map (s ≫ Descent.GaloisHom.hom r hf)).hom.hom = (F.map (𝟙 S)).hom.hom
  rw [Functor.map_comp, Descent.GaloisHom.baseChange_hom, hr, F.map_id]

end Perfect

section Split

variable {k : Type u} [Field k] {G S Q : GroupScheme (Spec (CommRingCat.of k))}
  [IsCommMonObj G.X]

/-- The multiplication `ker r × S → G` of a split commutative extension is an isomorphism. -/
theorem isIso_subgroupMultiplication_kernelι (s : S ⟶ G) (r : G ⟶ S) (hr : s ≫ r = 𝟙 S) :
    IsIso (subgroupMultiplication (kernelι r) s) := by
  have h := CommutativeSplitProduct.iso_hom_points r s hr _ (𝟙 _)
  have he : subgroupMultiplication (kernelι r) s =
      (CommutativeSplitProduct.iso r s hr).hom.hom.hom := by
    rw [← Category.id_comp (CommutativeSplitProduct.iso r s hr).hom.hom.hom, h]
    simp only [Category.id_comp]
    rfl
  rw [he]
  exact (inferInstance : IsIso ((Grp.forget _).mapIso (CommutativeSplitProduct.iso r s hr)).hom)

/-- If `s` has a retraction `r` and `q : G ⟶ Q` is an fppf quotient map with kernel `S` and
unipotent target, then `ker r` is unipotent. -/
theorem isUnipotent_kernel_of_retraction (s : S ⟶ G) (r : G ⟶ S) (hr : s ≫ r = 𝟙 S)
    (q : G ⟶ Q) (hq : IsFppfQuotient (SubgroupFunctor.range s) q) (hQ : IsUnipotent Q) :
    IsUnipotent (kernel r) := by
  let u := kernelι r
  have : IsIso (subgroupMultiplication u s) := isIso_subgroupMultiplication_kernelι s r hr
  have := isIso_commutingSubgroupMultiplicationHom u s
  let p := commutingFactorRetraction u s (commute_of_isCommMonObj u s)
  have hk : kernelι q ≫ p = 0 := by
    apply AffineQuotient.kernelι_comp_eq_zero
    rw [hq.2.2.2]
    intro T x hx
    exact (mem_range_kernelι_iff p x).mpr
      ((comp_commutingFactorRetraction_eq_one_iff u s (commute_of_isCommMonObj u s) x).mpr hx)
  have : Flat q.hom.hom.left := hq.1
  have : Surjective q.hom.hom.left := hq.2.1
  have : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  let p' := FppfHomDescent.hom q p hk
  have hsec : (u ≫ q).hom.hom.left ≫ p'.hom.hom.left = 𝟙 _ := by
    have h1 : u ≫ q ≫ p' = 𝟙 _ := by
      rw [FppfHomDescent.fac q p hk]
      exact comp_commutingFactorRetraction u s (commute_of_isCommMonObj u s)
    have h2 := congrArg (fun φ => φ.hom.hom.left) h1
    change ((u ≫ q) ≫ p').hom.hom.left = (𝟙 (kernel r) : kernel r ⟶ kernel r).hom.hom.left
    rw [Category.assoc]
    exact h2
  have : IsSplitEpi p'.hom.hom.left := IsSplitEpi.mk' ⟨_, hsec⟩
  exact IsUnipotent.of_epi hQ p'

end Split

section Existence

variable {k : Type u} [Field k]

/-- **Milne 2017, Theorem 16.13(b), existence.** A commutative affine algebraic group over a
perfect field is the product, under multiplication, of a unipotent closed subgroup and a closed
subgroup of multiplicative type. -/
theorem exists_multiplicativeUnipotentDecomposition [PerfectField k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom] [IsCommMonObj G.X] :
    ∃ (U S : GroupScheme (Spec (CommRingCat.of k))) (u : U ⟶ G) (s : S ⟶ G),
      IsClosedSubgroup u ∧ IsUnipotent U ∧ IsClosedSubgroup s ∧ IsMultiplicativeType S ∧
        IsIso (subgroupMultiplication u s) := by
  obtain ⟨S, Q, s, q, hs, hS, -, hq, hQ, -, hQa⟩ := exists_multiplicativePart G
  have := hQa
  have : IsAffineHom S.X.hom := hS.isAffineHom
  obtain ⟨r, hr⟩ := exists_retraction_of_perfectField s hs hS q hq hQ
  exact ⟨kernel r, S, kernelι r, s, isClosedSubgroup_kernelι r,
    isUnipotent_kernel_of_retraction s r hr q hq hQ, hs, hS,
    isIso_subgroupMultiplication_kernelι s r hr⟩

end Existence

end CommutativeDecomposition

end Langlands.GroupScheme
