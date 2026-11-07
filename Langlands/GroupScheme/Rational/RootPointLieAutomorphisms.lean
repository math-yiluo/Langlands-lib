import Langlands.GroupScheme.Rational.RootPointLieEquiv
import Langlands.GroupScheme.Rational.VectorPointLieNaturality
import Langlands.GroupScheme.Rational.RootSubgroupAutomorphismRigidity
import Langlands.GroupScheme.Rational.RootSubgroupCentralizerAction
import Langlands.GroupScheme.AutomorphicActionPointIso

/-! # Actual root-point Lie comparison under torus-fixing automorphisms -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

section OverBase

variable {B : Scheme.{u}} {S : CommGroupScheme B} {G : GroupScheme B}
    (i : S.toGrp ⟶ G) (a : characterLattice S)

/-- Postcomposition by a torus-fixing automorphism on the actual root subgroup
points, on every test scheme. -/
def rootPointsAutOfFixesTorus (σ : G ≅ G) (hi : i ≫ σ.hom = i) (X : Over B) :
    MulAut ((subgroup i a).carrier X) where
  toFun x := ⟨x.val ≫ σ.hom.hom.hom,
    comp_mem_subgroup_of_fixes_torus i σ.hom hi a x.property⟩
  invFun x := ⟨x.val ≫ σ.inv.hom.hom,
    comp_mem_subgroup_of_fixes_torus i σ.inv (fixes_torus_inv i σ hi) a x.property⟩
  left_inv x := by
    apply Subtype.ext
    change (x.val ≫ σ.hom.hom.hom) ≫ σ.inv.hom.hom = x.val
    rw [Category.assoc, ← Grp.comp_hom_hom, σ.hom_inv_id, Grp.id_hom_hom,
      Category.comp_id]
  right_inv x := by
    apply Subtype.ext
    change (x.val ≫ σ.inv.hom.hom) ≫ σ.hom.hom.hom = x.val
    rw [Category.assoc, ← Grp.comp_hom_hom, σ.inv_hom_id, Grp.id_hom_hom,
      Category.comp_id]
  map_mul' x y := Subtype.ext (MonObj.mul_comp x.val y.val σ.hom.hom.hom)

@[simp]
theorem rootPointsAutOfFixesTorus_val (σ : G ≅ G) (hi : i ≫ σ.hom = i)
    (X : Over B) (x : (subgroup i a).carrier X) :
    (rootPointsAutOfFixesTorus i a σ hi X x).val = x.val ≫ σ.hom.hom.hom := rfl

variable {H : GroupScheme B} (b : AutomorphicAction H G)
    (hfix : ∀ (X : Over B) (h : X ⟶ H.X) (s : X ⟶ S.X),
      b.act h (s ≫ i.hom.hom) = s ≫ i.hom.hom)

/-- An action fixing the torus acts on its intrinsic root subgroup points. -/
def rootPointsActionOfFixesTorus (X : Over B) (h : X ⟶ H.X) :
    MulAut ((subgroup i a).carrier X) where
  toFun x := ⟨b.act h x.val, subgroup_isStable_of_fixes_torus b i hfix a X h x.val x.property⟩
  invFun x := ⟨b.act h⁻¹ x.val,
    subgroup_isStable_of_fixes_torus b i hfix a X h⁻¹ x.val x.property⟩
  left_inv x := Subtype.ext (b.act_inv_act h x.val)
  right_inv x := Subtype.ext (b.act_act_inv h x.val)
  map_mul' x y := Subtype.ext (b.act_mul_right h x.val y.val)

include hfix in
/-- Evaluation of an action fixing the torus fixes its actual torus morphism. -/
theorem basePointIso_fixes_torus (h : Over.mk (𝟙 B) ⟶ H.X) :
    i ≫ (b.basePointIso h).hom = i := by
  apply Grp.hom_ext
  change i.hom.hom ≫ (b.basePointIso h).hom.hom.hom = i.hom.hom
  rw [b.comp_basePointIso_hom]
  simpa only [Category.id_comp] using hfix S.X (H.constantPoint h S.X) (𝟙 S.X)

end OverBase

section Field

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    {a : characterLattice S} (ha : a ≠ 0) (hhigh : HasNoHigherRoots i a)
    (σ : G ≅ G) (hi : i ≫ σ.hom = i)

variable {U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom U.X.hom]
    {j : U ⟶ G} (hj : (subgroup i a).IsRepresentedBy j)

/-- The represented root-point comparison intertwines an actual ambient
torus-fixing automorphism with its actual differential. -/
theorem representedRootPointLieEquiv_aut_apply (x : rationalPoints U) :
    (representedRootPointLieEquiv hS i ha hhigh hj
      (Additive.ofMul (rootPointsAutOfFixesTorus i a σ hi _
        (hj.pointsEquiv _ x))) : Additive (lieKernel G k)) =
      Lie.targetMapLinear σ.hom k
        (representedRootPointLieEquiv hS i ha hhigh hj
          (Additive.ofMul (hj.pointsEquiv _ x))) := by
  let q := rootIsoOfFixesTorus i a j hj σ hi
  have hcomp : q.hom ≫ j = j ≫ σ.hom :=
    rootHomOfFixesTorus_comp i a j hj σ.hom hi
  have hp : rootPointsAutOfFixesTorus i a σ hi _ (hj.pointsEquiv _ x) =
      hj.pointsEquiv _ (rationalPoints.map q.hom x) := by
    apply Subtype.ext
    change (x ≫ j.hom.hom) ≫ σ.hom.hom.hom =
      (x ≫ q.hom.hom.hom) ≫ j.hom.hom
    simpa only [Grp.comp_hom_hom, Category.assoc] using
      (congrArg (fun f : U ⟶ G => x ≫ f.hom.hom) hcomp).symm
  let c := weightVectorCoordinatesOfNoHigherRoots hS i ha hhigh hj
  have hnat := vectorPointLieEquiv_equivariantIso hS ha c.2.property c.2.property q
    (rootIsoOfFixesTorus_equivariant i a j hj σ hi) (CommAlgCat.of k k)
    (Additive.ofMul (GaloisPointComparison.rationalCoeffEquiv k U x))
  simp only [toMul_ofMul] at hnat
  have haff : GaloisPointComparison.rationalCoeffEquiv k U (rationalPoints.map q.hom x) =
      GaloisPointComparison.rationalCoeffEquiv k U x ≫ q.hom.hom.hom :=
    GaloisPointComparison.rationalCoeffEquiv_map k q.hom x
  rw [hp, representedRootPointLieEquiv_apply, representedRootPointLieEquiv_apply]
  change Lie.targetMapLinear j k
      (vectorPointLieEquiv c.2.val c.2.property.1 (CommAlgCat.of k k)
        (Additive.ofMul (GaloisPointComparison.rationalCoeffEquiv k U
          (rationalPoints.map q.hom x)))) =
    Lie.targetMapLinear σ.hom k (Lie.targetMapLinear j k
      (vectorPointLieEquiv c.2.val c.2.property.1 (CommAlgCat.of k k)
        (Additive.ofMul (GaloisPointComparison.rationalCoeffEquiv k U x))))
  calc
    _ = Lie.targetMapLinear j k (Lie.targetMapLinear q.hom k
        (vectorPointLieEquiv c.2.val c.2.property.1 (CommAlgCat.of k k)
          (Additive.ofMul (GaloisPointComparison.rationalCoeffEquiv k U x)))) := by
      simpa only [haff] using (congrArg (Lie.targetMapLinear j k) hnat).symm
    _ = _ := by
      apply Additive.toMul.injective
      apply Subtype.ext
      simpa only [lieKernelTargetLinear_val, Grp.comp_hom_hom, Category.assoc] using
        congrArg (fun f : U ⟶ G =>
          (vectorPointLieEquiv c.2.val c.2.property.1 (CommAlgCat.of k k)
            (Additive.ofMul (GaloisPointComparison.rationalCoeffEquiv k U x))).toMul.val ≫
              f.hom.hom) hcomp

omit [IsAffineHom U.X.hom] in
/-- The intrinsic comparison commutes with every torus-fixing ambient automorphism. -/
theorem rootPointLieEquiv_aut
    (v : Additive ((subgroup i a).carrier (Over.mk (𝟙 _)))) :
    (rootPointLieEquiv hS i ha hhigh
      (Additive.ofMul (rootPointsAutOfFixesTorus i a σ hi _ v.toMul)) :
        Additive (lieKernel G k)) =
      Lie.targetMapLinear σ.hom k (rootPointLieEquiv hS i ha hhigh v) := by
  obtain ⟨U, hU, j, hj, h⟩ := rootPointLieEquiv_exists_representative hS i ha hhigh
  let : IsAffineHom U.X.hom := hU
  rw [h]
  let x := (hj.pointsEquiv _).symm v.toMul
  have hx : hj.pointsEquiv _ x = v.toMul := (hj.pointsEquiv _).apply_symm_apply _
  simpa only [hx, ofMul_toMul] using
    representedRootPointLieEquiv_aut_apply hS i ha hhigh σ hi hj x

omit [IsAffineHom U.X.hom] in
/-- The actual action of any torus-fixing group on root points becomes its
actual differential under the intrinsic point-to-Lie comparison. -/
theorem rootPointLieEquiv_act
    {H : GroupScheme (Spec (CommRingCat.of k))} (b : AutomorphicAction H G)
    (hfix : ∀ (X : Over (Spec (CommRingCat.of k)))
      (h : X ⟶ H.X) (s : X ⟶ S.X),
      b.act h (s ≫ i.hom.hom) = s ≫ i.hom.hom)
    (h : rationalPoints H) (v : Additive ((subgroup i a).carrier (Over.mk (𝟙 _)))) :
    (rootPointLieEquiv hS i ha hhigh
      (Additive.ofMul (rootPointsActionOfFixesTorus i a b hfix _ h v.toMul)) :
        Additive (lieKernel G k)) =
      b.differential (GaloisPointComparison.rationalCoeffEquiv k H h)
        (rootPointLieEquiv hS i ha hhigh v) := by
  have hbase : H.constantPoint h (Over.mk (𝟙 (Spec (CommRingCat.of k)))) = h := by
    dsimp only [constantPoint]
    have he : Over.homMk (𝟙 (Spec (CommRingCat.of k))) (by simp) =
        𝟙 (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
      apply Over.OverMorphism.ext
      rfl
    exact (congrArg (fun f : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      Over.mk (𝟙 (Spec (CommRingCat.of k))) => f ≫ h) he).trans (Category.id_comp h)
  have hact : rootPointsAutOfFixesTorus i a (b.basePointIso h)
      (basePointIso_fixes_torus i b hfix h) _ v.toMul =
      rootPointsActionOfFixesTorus i a b hfix _ h v.toMul := by
    apply Subtype.ext
    change v.toMul.val ≫ (b.basePointIso h).hom.hom.hom = b.act h v.toMul.val
    rw [b.comp_basePointIso_hom, hbase]
  have hcoeff : H.constantPoint h
      ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k k))) =
      GaloisPointComparison.rationalCoeffEquiv k H h := by
    apply Over.OverMorphism.ext
    rw [GaloisPointComparison.rationalCoeffEquiv_left]
    change Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫ h.left = h.left
    simp
  have hnat := rootPointLieEquiv_aut hS i ha hhigh (b.basePointIso h)
    (basePointIso_fixes_torus i b hfix h) v
  rw [hact, b.targetMapLinear_basePointIso, hcoeff] at hnat
  exact hnat

end Field

end Langlands.GroupScheme.RelativeRoot
