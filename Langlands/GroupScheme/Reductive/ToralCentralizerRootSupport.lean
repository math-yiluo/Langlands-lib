import Langlands.GroupScheme.Torus.MultiplicativeTypeAbsoluteEquivalenceProof
import Langlands.Representation.Category.Subquotients
import Langlands.GroupScheme.Reductive.SplitSemisimpleRootSpanSufficiency
import Langlands.GroupScheme.Rational.RootKernelIdentityWeights
import Langlands.GroupScheme.Rational.TorusCentralizerFactorization
import Langlands.GroupScheme.Torus.WeightRestriction

/-! # Toral character quotients and the roots of a centralizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

/-- A Galois-stable submodule of the absolute characters of a torus is the
kernel of restriction along a ground-field homomorphism of multiplicative type. -/
theorem exists_multiplicativeType_characterKernel {k : Type u} [Field k]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsTorus T.toGrp)
    (L : Submodule ℤ
      (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj T)))
    (hL : ∀ (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) χ, χ ∈ L →
      characterLattice.galoisRepresentation k (SeparableClosure k) T σ χ ∈ L) :
    ∃ (N : CommGroupScheme (Spec (CommRingCat.of k))) (n : N ⟶ T),
      IsMultiplicativeType N.toGrp ∧
      ∀ χ, (CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).map n ≫ χ = 0 ↔
        χ ∈ L := by
  let X := MultiplicativeTypeGroup.characterFunctor k
  let : X.IsEquivalence := multiplicativeTypeAbsoluteEquivalence k
  let T' : MultiplicativeTypeGroup k := ⟨T, hT.isMultiplicativeType⟩
  let A := X.obj (op T')
  let S : Subrepresentation A.representation :=
    { toSubmodule := L, apply_mem_toSubmodule := hL }
  let Q : FGDiscreteGaloisModule k :=
    ⟨Langlands.SmoothRep.quotient A.obj S,
      inferInstanceAs (Module.Finite ℤ (A ⧸ L))⟩
  let p : A ⟶ Q := ObjectProperty.homMk (Langlands.SmoothRep.mkQ A.obj S)
  let N' := X.asEquivalence.inverse.obj Q
  let e : X.obj N' ≅ Q := X.asEquivalence.counitIso.app Q
  let g : op T' ⟶ N' := X.preimage (p ≫ e.inv)
  let n := g.unop.hom
  refine ⟨N'.unop.obj, n, N'.unop.property, fun χ => ?_⟩
  have hn : X.map g ≫ e.hom = p := by
    dsimp only [g]
    rw [Functor.map_preimage, Category.assoc, e.inv_hom_id, Category.comp_id]
  have hinj : Function.Injective (FGDiscreteGaloisModule.hom e.hom) := by
    intro x y hxy
    have he : ∀ z, FGDiscreteGaloisModule.hom e.inv (FGDiscreteGaloisModule.hom e.hom z) = z := by
      intro z
      exact congrArg (fun f => FGDiscreteGaloisModule.hom f z) e.hom_inv_id
    rw [← he x, ← he y, hxy]
  change FGDiscreteGaloisModule.hom (X.map g) χ = 0 ↔ χ ∈ L
  rw [← (hinj.eq_iff), map_zero]
  change FGDiscreteGaloisModule.hom (X.map g ≫ e.hom) χ = 0 ↔ χ ∈ L
  rw [hn]
  exact Submodule.Quotient.mk_eq_zero L

section Field

variable {k : Type u} [Field k]
  {G C H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom C.X.hom] [LocallyOfFiniteType C.X.hom]
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
  {N T : CommGroupScheme (Spec (CommRingCat.of k))} [IsAffineHom N.X.hom]

/-- The roots in an open subgroup of the centralizer of a toral image are
exactly the ambient roots whose characters are trivial on that image. The
torus and its character lattice are kept throughout the comparison. -/
theorem roots_of_open_toralCentralizer
    (n : N ⟶ T) (i : T.toGrp ⟶ G) (l : H ⟶ C) (j : C ⟶ G)
    [IsOpenImmersion l.hom.hom.left] (f : T.toGrp ⟶ H) (hf : f ≫ l ≫ j = i)
    (hT : IsSplitTorus T.toGrp)
    (hj : (torusCentralizer (CommGroupScheme.groupHom n ≫ i)).IsRepresentedBy j) :
    roots f = {χ | χ ∈ roots i ∧ n ≫ χ = 0} := by
  let m := CommGroupScheme.groupHom n
  have hcen : IsCentral (m ≫ f ≫ l) := by
    apply isCentral_of_range_le_torusCentralizer hj.1
    simpa only [Category.assoc, hf, m] using hj.2.le
  have : Mono j.hom.hom := hj.1
  have : Mono l.hom.hom := Over.mono_of_mono_left _
  ext χ
  constructor
  · intro hχ
    have hC : χ ∈ roots (f ≫ l) := roots_subset_comp l f hχ
    have hG : χ ∈ roots i := by
      rw [← hf, ← Category.assoc]
      exact roots_subset_comp j (f ≫ l) hC
    refine ⟨hG, ?_⟩
    have : IsAffine N.X.left := isAffine_of_isAffineHom N.X.hom
    have hv := pointCharacters_root_eq_one_of_isCentral (f ≫ l) m hcen N.X (𝟙 N.X) hC
    rw [Category.id_comp, characterLattice.pointCharacters_apply] at hv
    apply CommGroupScheme.hom_ext_points
    intro U x
    have hpt : (𝟙 N.X) ≫ (CommGroupScheme.groupHom (n ≫ χ)).hom.hom = 1 := by
      apply (Gm.pointsEquiv _ N.X).injective
      rw [comp_groupHom_comp, Category.id_comp, map_one]
      exact hv
    have he := congrArg (fun y : N.X ⟶ (Gm _).X => x ≫ y) hpt
    simpa only [← Category.assoc, Category.comp_id, comp_groupHom_zero, MonObj.comp_one] using he
  · rintro ⟨hχ, hzero⟩
    obtain ⟨x, hx, hx₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ.2
    have hx' : x ∈ weightSpace (m ≫ i) 0 := by
      have h := weightSpace_le_comp n i χ hx
      rwa [hzero] at h
    have hxc := Lie.mem_torusCentralizer_of_mem_weightSpace_zero (m ≫ i) x.toMul hx'
    have hLie : RelativeRoot.HasLieImage (torusCentralizer (m ≫ i))
        (LinearMap.range (Lie.targetMapLinear j k)) :=
      RelativeRoot.hasLieImage_of_isRepresentedBy j hj
    have hxr : x ∈ LinearMap.range (Lie.targetMapLinear (l ≫ j) k) := by
      rw [Lie.targetMapLinear_comp, LinearMap.range_comp_of_range_eq_top _
        (LinearMap.range_eq_top.mpr (Lie.targetMapLinear_surjective_of_smooth l k inferInstance))]
      exact (hLie x).mp hxc
    have hx'' : x ∈ weightSpace (f ≫ l ≫ j) χ := hf ▸ hx
    obtain ⟨y, hy, hxy⟩ := Lie.exists_weightSpace_preimage (l ≫ j) f hT hx'' hxr
    refine ⟨hχ.1, ?_⟩
    intro hy₀
    rw [hy₀, Submodule.mem_bot] at hy
    rw [hy, map_zero] at hxy
    exact hx₀ hxy.symm

end Field

end Langlands.GroupScheme
