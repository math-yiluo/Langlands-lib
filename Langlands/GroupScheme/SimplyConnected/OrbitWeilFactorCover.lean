import Langlands.GroupScheme.SimplyConnected.OrbitWeilInclusion

/-! # Actual simply connected covers with a prescribed geometric Weil factor -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000

namespace Langlands.GroupScheme.SimplyConnectedAlmostSimpleProduct

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom]
  [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom]
  (D : SimplyConnectedAlmostSimpleProduct
    ((GroupScheme.baseChange (algebraBaseMap k L)).obj G))
  [IsGalois k L] [IsAffineHom G.X.hom]
  [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
  [LocallyOfFinitePresentation G.X.hom] [IsSepClosed L]

attribute [local instance] factorStabilizerDescent_isAffine
  factorStabilizerDescent_locallyOfFiniteType

local instance orbitWeilCover_baseSurjective : Surjective (algebraBaseMap k L) :=
  (fieldExtension_fpqc k L).1

local instance orbitWeilCover_baseFlat : Flat (algebraBaseMap k L) :=
  (fieldExtension_fpqc k L).2.1

local instance orbitWeilCover_baseQuasiCompact : QuasiCompact (algebraBaseMap k L) :=
  (fieldExtension_fpqc k L).2.2

/-- The geometric Weil source is exactly the original orbit subproduct. -/
def orbitWeilBaseChangeIso (i : D.Index) :
    (GroupScheme.baseChange (algebraBaseMap k L)).obj
        (AffineWeil.groupScheme k (D.factorStabilizerField i) (D.factorStabilizerDescent i).1) ≅
      D.subproduct (D.galoisFactorOrbit i) :=
  D.stabilizerEmbeddingProductIso i ≪≫ D.embeddingConjugateOrbitIso i

/-- The selected actual Weil subgroup is closed over the original field. -/
theorem isClosedSubgroup_orbitWeilInclusion (i : D.Index) :
    IsClosedSubgroup (D.orbitWeilInclusion i) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  apply IsClosedSubgroup.of_baseChange_of_isAffine (algebraBaseMap k L)
  rw [D.orbitWeilInclusion_baseChange, embeddingConjugateOrbitInclusion, ← Category.assoc]
  exact IsClosedSubgroup.iso_comp (D.orbitWeilBaseChangeIso i)
    (D.isClosedSubgroup_subproductInclusion (D.galoisFactorOrbit i))

/-- Its scalar-extended all-test range is precisely the original orbit range. -/
theorem range_orbitWeilInclusion_baseChange (i : D.Index) :
    (SubgroupFunctor.range (D.orbitWeilInclusion i)).baseChange (algebraBaseMap k L) =
      SubgroupFunctor.range (D.subproductInclusion (D.galoisFactorOrbit i)) := by
  rw [← SubgroupFunctor.range_baseChangeHom, D.orbitWeilInclusion_baseChange,
    embeddingConjugateOrbitInclusion, ← Category.assoc]
  exact SubgroupFunctor.range_iso_comp (D.orbitWeilBaseChangeIso i) _

/-- The actual Weil inclusion is normal on every test scheme over the
original field. -/
theorem isNormal_range_orbitWeilInclusion (i : D.Index) :
    (SubgroupFunctor.range (D.orbitWeilInclusion i)).IsNormal := by
  let : IsClosedImmersion (D.orbitWeilInclusion i).hom.hom.left :=
    D.isClosedSubgroup_orbitWeilInclusion i
  let : Mono (D.orbitWeilInclusion i).hom.hom := Over.mono_of_mono_left _
  apply SubgroupFunctor.isNormal_range_of_baseChange (algebraBaseMap k L)
    (D.orbitWeilInclusion i)
  rw [D.range_orbitWeilInclusion_baseChange]
  exact D.isNormal_range_subproductInclusion (D.galoisFactorOrbit i)

/-- The original actual Weil subgroup is smooth, detected on its geometric
orbit-product presentation. -/
theorem smooth_orbitWeilGroup (i : D.Index) :
    Smooth
      (AffineWeil.groupScheme k (D.factorStabilizerField i) (D.factorStabilizerDescent i).1).X.hom := by
  let W := AffineWeil.groupScheme k (D.factorStabilizerField i) (D.factorStabilizerDescent i).1
  let e := D.orbitWeilBaseChangeIso i
  let : Smooth (D.subproduct (D.galoisFactorOrbit i)).X.hom :=
    D.smooth_subproduct (D.galoisFactorOrbit i)
  have hsm : Smooth ((GroupScheme.baseChange (algebraBaseMap k L)).obj W).X.hom := by
    rw [← e.hom.hom.hom.w]
    infer_instance
  exact smooth_of_baseChange (algebraBaseMap k L) W hsm

/-- The original actual Weil subgroup is connected, detected on its
geometrically connected orbit-product presentation. -/
theorem connectedSpace_orbitWeilGroup (i : D.Index) :
    ConnectedSpace
      (AffineWeil.groupScheme k (D.factorStabilizerField i) (D.factorStabilizerDescent i).1).X.left := by
  let W := AffineWeil.groupScheme k (D.factorStabilizerField i) (D.factorStabilizerDescent i).1
  let e := D.orbitWeilBaseChangeIso i
  let : ConnectedSpace (D.subproduct (D.galoisFactorOrbit i)).X.left :=
    D.connectedSpace_subproduct (D.galoisFactorOrbit i)
  have hc : ConnectedSpace ((GroupScheme.baseChange (algebraBaseMap k L)).obj W).X.left :=
    e.hom.hom.hom.left.homeomorph.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_of_baseChange (algebraBaseMap k L) W hc

/-- An actual simply connected product complement to the selected orbit's
actual ground-field Weil subgroup. -/
structure OrbitWeilComplement (i : D.Index) where
  group : GroupScheme (Spec (CommRingCat.of k))
  simplyConnected : IsSimplyConnected group
  iso : AffineWeil.groupScheme k (D.factorStabilizerField i)
    (D.factorStabilizerDescent i).1 ⊗ group ≅ G
  left_eq : lift (𝟙 _) (Grp.homMk (toUnit _ ≫ η[group.X])) ≫ iso.hom =
    D.orbitWeilInclusion i

/-- Simple connectedness upgrades the normal complement's central isogeny to
an actual product isomorphism with the prescribed Weil inclusion. -/
theorem nonempty_orbitWeilComplement (hG : IsSimplyConnected G) (i : D.Index) :
    Nonempty (D.OrbitWeilComplement i) := by
  let W := AffineWeil.groupScheme k (D.factorStabilizerField i) (D.factorStabilizerDescent i).1
  obtain ⟨hW, N, n, hN, _hn, _hnormal, hprod, hc, hm⟩ :=
    semisimpleNormalIsogenyComplement k G W hG.isSemisimple (D.orbitWeilInclusion i)
      (D.isClosedSubgroup_orbitWeilInclusion i) (D.smooth_orbitWeilGroup i)
      (D.connectedSpace_orbitWeilGroup i) (D.isNormal_range_orbitWeilInclusion i)
  let m := commutingSubgroupMultiplicationHom (D.orbitWeilInclusion i) n hc
  have : IsIso m := hG.central_isogeny_isIso _ m hprod hm
  have hscProd : IsSimplyConnected (W ⊗ N) := hG.of_iso (asIso m)
  refine ⟨{
    group := N
    simplyConnected := hscProd.of_tensor_right hW hN
    iso := asIso m
    left_eq := ?_ }⟩
  apply Grp.hom_ext
  change lift (𝟙 W.X) (toUnit _ ≫ η[N.X]) ≫
    subgroupMultiplication (D.orbitWeilInclusion i) n = (D.orbitWeilInclusion i).hom.hom
  rw [comp_subgroupMultiplication, Category.id_comp]
  change (D.orbitWeilInclusion i).hom.hom * ((1 : W.X ⟶ N.X) ≫ n.hom.hom) = _
  rw [MonObj.one_comp, mul_one]

/-- Choose the complement without changing the selected extension-field model. -/
def orbitWeilComplement (hG : IsSimplyConnected G) (i : D.Index) : D.OrbitWeilComplement i :=
  Classical.choice (D.nonempty_orbitWeilComplement hG i)

/-- The actual covering factor for a prescribed geometric factor of the whole
simply connected group, retaining its exact stabilizer field and descended group. -/
def orbitWeilFactor (hG : IsSimplyConnected G) (i : D.Index) :
    SimplyConnectedWeilFactor (D.orbitWeilInclusion i) where
  extension := D.factorStabilizerField i
  factor := (D.factorStabilizerDescent i).1
  simplyConnected := D.isSimplyConnected_factorStabilizerDescent i
  absolutelyAlmostSimple := D.isAbsolutelyAlmostSimple_factorStabilizerDescent_of_isSepClosed i
  weilIso := Iso.refl _
  complement := (D.orbitWeilComplement hG i).group
  complement_simplyConnected := (D.orbitWeilComplement hG i).simplyConnected
  productIso := (D.orbitWeilComplement hG i).iso
  product_simplyConnected := hG.of_iso (D.orbitWeilComplement hG i).iso
  left_eq := by
    simpa only [Iso.refl_inv, Category.id_comp] using (D.orbitWeilComplement hG i).left_eq

@[simp] theorem orbitWeilFactor_extension (hG : IsSimplyConnected G) (i : D.Index) :
    (D.orbitWeilFactor hG i).extension = D.factorStabilizerField i := rfl

@[simp] theorem orbitWeilFactor_factor (hG : IsSimplyConnected G) (i : D.Index) :
    (D.orbitWeilFactor hG i).factor = (D.factorStabilizerDescent i).1 := rfl

end Langlands.GroupScheme.SimplyConnectedAlmostSimpleProduct
