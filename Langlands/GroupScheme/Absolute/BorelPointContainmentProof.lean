import Langlands.GroupScheme.Absolute.BorelPointContainmentTangent
import Langlands.GroupScheme.Absolute.BorelPointContainmentWeights
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Rational.TorusCentralizer
import Langlands.GroupScheme.SmoothProducts
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Lie.DimensionInduction
import Langlands.GroupScheme.Absolute.BorelContaining
import Langlands.GroupScheme.Rational.WeylTorusNorm
import Langlands.GroupScheme.Rational.RootAnnihilatorCentralityStatement
import Langlands.GroupScheme.Nilpotent.EmptyRoots
import Langlands.GroupScheme.Nilpotent.Basic
import Langlands.GroupScheme.Torus.ExistenceProof
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof

/-! # Proof: every rational point lies in a Borel subgroup -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace BorelPointContainment

open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.TangentSmoothness

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

/-- **Density of the conjugation map of a dynamic centralizer.** Let `G` be a smooth connected
affine group over an algebraically closed field, `χ` a cocharacter of `G` and `iZ : Z ⟶ G` a
smooth affine representative of its dynamic centralizer. Then the conjugation map
`G × Z ⟶ G`, `(x, z) ↦ x iZ(z) x⁻¹`, has dense range. -/
theorem denseRange_conjugation_centralizer [IsAlgClosed k]
    {G Z : GroupScheme (Spec (CommRingCat.of k))} [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [ConnectedSpace G.X.left] [Smooth Z.X.hom] [IsAffineHom Z.X.hom]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (iZ : Z ⟶ G)
    (hZ : (Dynamic.centralizer χ).IsRepresentedBy iZ) :
    DenseRange (conjugation iZ).left := by
  let P := (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) k))
  have hP : P.hom = 𝟙 _ := by
    simp [P, algSpec_obj_hom, Algebra.algebraMap_self]
    rfl
  let e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P :=
    Over.homMk (𝟙 _) (by rw [hP]; rfl)
  have hconst : ∀ y : P ⟶ G.X, G.constantPoint (e ≫ y) P = y := by
    intro y
    unfold constantPoint
    rw [← Category.assoc]
    convert Category.id_comp y
    apply Over.OverMorphism.ext
    simp [e, hP]
  obtain ⟨u, hu⟩ := exists_generic_affinePoint (k := k) (G := G) χ
  have hχZ : SubgroupFunctor.range χ ≤ Dynamic.centralizer χ := by
    rw [← torusCentralizer_gm_eq_dynamicCentralizer]
    exact range_le_torusCentralizer χ
  let χ' := hZ.factorHom χ hχZ
  have hχ' : χ' ≫ iZ = χ := hZ.factorHom_comp χ hχZ
  let z₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Z.X := (e ≫ u⁻¹) ≫ χ'.hom.hom
  have hz₀ : G.constantPoint (z₀ ≫ iZ.hom.hom) P = (u ≫ χ.hom.hom)⁻¹ := by
    have h : z₀ ≫ iZ.hom.hom = e ≫ (u ≫ χ.hom.hom)⁻¹ := by
      rw [Category.assoc, ← Grp.comp_hom_hom, hχ']
      simp only [GrpObj.comp_inv, GrpObj.inv_comp, Category.assoc]
    rw [h, hconst]
  have : Smooth (G.X ⊗ Z.X).hom := smooth_tensor _ _ inferInstance inferInstance
  have : IrreducibleSpace G.X.left := DynamicConnected.irreducibleSpace_of_smooth G
  refine denseRange_of_isTangentSurjectiveAt _ (Over.w _)
    (Over.w (lift 1 z₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X ⊗ Z.X))
    (isTangentSurjectiveAt_conjugation iZ z₀ fun W => ?_)
  obtain ⟨X, ξ, h⟩ := exists_adjoint_sub_add_eq χ iZ hZ u hu (Additive.ofMul W)
  refine ⟨X.toMul, ξ.toMul, ?_⟩
  rw [hz₀, inv_inv]
  have h' := congrArg Additive.toMul h
  rw [toMul_add, toMul_sub, adjoint_toMul, lieKernelTargetLinear_toMul, toMul_ofMul] at h'
  rw [← h', div_eq_mul_inv, mul_right_comm]

/-- **The central case.** If every cocharacter of a smooth connected affine group `G` over an
algebraically closed field is central, then `G` is solvable, so the identity of `G` is a Borel
subgroup. -/
theorem isBorelSubgroup_id_of_forall_centralizer_eq_top [IsAlgClosed k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [ConnectedSpace G.X.left]
    (hc : ∀ χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G, Dynamic.centralizer χ = ⊤) :
    IsBorelSubgroup (𝟙 G) := by
  obtain ⟨T₀, j₀, hj₀⟩ := TorusExistence.exists_isMaximalTorus G
  have hTs := hj₀.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  have hcen : IsCentral j₀ := isCentral_of_forall_cocharacter hTs j₀ fun ν =>
    (isCentral_iff_dynamicCentralizer_eq_top _).2 (hc _)
  have hsolv : IsSolvableGroupScheme G :=
    (hj₀.isNilpotentGroupScheme_of_isCentral_of_isAlgClosed hcen).isSolvableGroupScheme
  refine ⟨?_, inferInstance, inferInstance, hsolv, ?_⟩
  · change IsClosedImmersion (𝟙 G.X.left)
    infer_instance
  · intro B' i' f hi' _ _ _ hf
    have : IsClosedImmersion i'.hom.hom.left := hi'
    have : Mono i'.hom.hom := Over.mono_of_mono_left _
    refine ⟨⟨i', hf, Grp.hom_ext _ _ ?_⟩⟩
    apply (cancel_mono i'.hom.hom).1
    rw [← Grp.comp_hom_hom, Category.assoc, hf, Category.comp_id, Grp.id_hom_hom,
      Category.id_comp]

end BorelPointContainment

open BorelPointContainment in
/-- **Every element lies in a Borel subgroup** (Milne, Corollary 17.34). -/
theorem borelPointContainment : BorelPointContainmentStatement.{u} := by
  intro k _ _ G _ _ _
  refine smoothConnectedAffineGroup_lieDimension_induction (k := k)
    (fun G => ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G)
        (b : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ B.X),
        IsBorelSubgroup i ∧ b ≫ i.hom.hom = g) ?_ G
  intro G _ _ _ ih g
  by_cases hc : ∀ χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G, Dynamic.centralizer χ = ⊤
  · exact ⟨G, 𝟙 G, g, isBorelSubgroup_id_of_forall_centralizer_eq_top hc, by
      rw [Grp.id_hom_hom, Category.comp_id]⟩
  push Not at hc
  obtain ⟨χ, hχ⟩ := hc
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let Z := Dynamic.Affine.centralizerScheme χ
  let iZ := Dynamic.Affine.centralizerHom χ
  have hZrep := Dynamic.Affine.isRepresentedBy_centralizerHom χ
  have hZc := Dynamic.Affine.isClosedSubgroup_centralizerHom χ
  have : IsAffineHom Z.X.hom := hZc.isAffineHom
  have : Smooth Z.X.hom := (dynamicSmooth k G χ Z iZ).2.1 hZrep
  have : ConnectedSpace Z.X.left := ((dynamicConnected k G χ Z iZ).2 inferInstance).2 hZrep
  have hnotiso : ¬ IsIso iZ := by
    intro h
    apply hχ
    rw [← hZrep.2]
    refine SubgroupFunctor.ext fun U => Subgroup.ext fun g => ⟨fun _ => Subgroup.mem_top g,
      fun _ => ?_⟩
    exact ⟨g ≫ (inv iZ).hom.hom, by
      change (g ≫ (inv iZ).hom.hom) ≫ iZ.hom.hom = g
      rw [Category.assoc, ← Grp.comp_hom_hom, IsIso.inv_hom_id, Grp.id_hom_hom,
        Category.comp_id]⟩
  have ihZ := ih Z (Lie.dimension_lt_of_proper_closedSubgroup iZ hZc hnotiso)
  refine exists_isBorelSubgroup_of_denseRange iZ
    (denseRange_conjugation_centralizer χ iZ hZrep) (fun h => ?_) g
  obtain ⟨B', i', b', hi', hb'⟩ := ihZ h
  obtain ⟨B, i, f, hi, hf⟩ := BorelExistence.exists_isBorelSubgroup_containing (i' ≫ iZ)
    ⟨hi'.isClosedSubgroup.comp hZc, hi'.smooth, hi'.connectedSpace, hi'.isSolvableGroupScheme⟩
  refine ⟨B, i, b' ≫ f.hom.hom, hi, ?_⟩
  rw [Category.assoc, ← Grp.comp_hom_hom, hf, Grp.comp_hom_hom, ← Category.assoc, hb']

end Langlands.GroupScheme
