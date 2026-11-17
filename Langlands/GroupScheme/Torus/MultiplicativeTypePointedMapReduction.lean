import Langlands.GroupScheme.Torus.MultiplicativeTypePointedMapStatement
import Langlands.GroupScheme.Torus.UnitsProductDecompositionStatement
import Langlands.GroupScheme.Torus.DiagonalizableCharacterProof
import Langlands.GroupScheme.Torus.DiagonalizableBaseChange
import Langlands.GroupScheme.Torus.PointedMorphismDescent
import Langlands.GroupScheme.FieldSeparatedProof
import Langlands.AlgebraicGeometry.SmoothPointedGeometricConnectedness

/-! # Pointed multiplicative-type maps from product-unit decomposition -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace PointedMapReduction

/-- A pointed scheme map multiplicative on every group of points is a group map. -/
theorem isMonHom_of_points {S : Scheme.{u}} {G H : GroupScheme S}
    (p : G.X ⟶ H.X) (hp : η[G.X] ≫ p = η[H.X])
    (hm : ∀ (U : Over S) (x y : U ⟶ G.X),
      (x * y) ≫ p = (x ≫ p) * (y ≫ p)) : IsMonHom p := by
  let F : ∀ U : Over S, (U ⟶ G.X) →* (U ⟶ H.X) := fun U =>
    { toFun := fun x => x ≫ p
      map_one' := by simp only [Hom.one_def, Category.assoc, hp]
      map_mul' := hm U }
  have hn : ∀ {U U' : Over S} (a : U' ⟶ U) (x : U ⟶ G.X),
      F U' (a ≫ x) = a ≫ F U x := fun a x => Category.assoc a x p
  have he : (homOfPoints F hn).hom.hom = p := by
    have h := comp_homOfPoints F hn G.X (𝟙 G.X)
    change 𝟙 G.X ≫ (homOfPoints F hn).hom.hom = 𝟙 G.X ≫ p at h
    simpa only [Category.id_comp] using h
  rw [← he]
  infer_instance

/-- The source of the rigidity theorem is integral, without an affine hypothesis. -/
theorem source_integral (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [ConnectedSpace G.X.left] : IsIntegral G.X.left :=
  Langlands.AlgebraicGeometry.connectedLocallyNoetherianDomainStalksIntegral
    G.X.left (LocallyOfFiniteType.isLocallyNoetherian G.X.hom) inferInstance
    (Langlands.AlgebraicGeometry.smoothDomainStalks k G.X.left G.X.hom inferInstance)

/-- Product-unit decomposition forces pointed maps to the multiplicative group
from smooth connected finite-type groups over algebraically closed fields to be homomorphisms. -/
theorem gm_isMonHom (hu : UnitsProductDecompositionStatement.{u})
    (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [QuasiCompact G.X.hom] [ConnectedSpace G.X.left]
    (p : G.X ⟶ (Gm (Spec (CommRingCat.of k))).X)
    (hp : η[G.X] ≫ p = η[(Gm (Spec (CommRingCat.of k))).X]) : IsMonHom p := by
  let : IsIntegral G.X.left := source_integral k G
  let : IsSeparated G.X.hom := fieldSeparated k G
  obtain ⟨a, b, hab⟩ := hu k G.X G.X inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance (μ[G.X] ≫ p)
  have h (U : Over (Spec (CommRingCat.of k))) (x y : U ⟶ G.X) :
      (x * y) ≫ p = (x ≫ a) * (y ≫ b) := by
    calc
      (x * y) ≫ p = lift x y ≫ (μ[G.X] ≫ p) := by
        rw [Hom.mul_def, Category.assoc]
      _ = (x ≫ a) * (y ≫ b) := by
        rw [hab, MonObj.comp_mul]
        simp only [← Category.assoc, lift_fst, lift_snd]
  have ho (U : Over (Spec (CommRingCat.of k))) : (1 : U ⟶ G.X) ≫ p = 1 := by
    simp only [Hom.one_def, Category.assoc, hp]
  apply isMonHom_of_points p hp
  intro U x y
  have h11 : ((1 : U ⟶ G.X) ≫ a) * ((1 : U ⟶ G.X) ≫ b) = 1 := by
    simpa only [one_mul, ho] using (h U 1 1).symm
  have hx1 : x ≫ p = (x ≫ a) * ((1 : U ⟶ G.X) ≫ b) := by
    simpa only [mul_one] using h U x 1
  have h1y : y ≫ p = ((1 : U ⟶ G.X) ≫ a) * (y ≫ b) := by
    simpa only [one_mul] using h U 1 y
  rw [h, hx1, h1y]
  calc
    (x ≫ a) * (y ≫ b) = ((x ≫ a) * (y ≫ b)) *
        (((1 : U ⟶ G.X) ≫ a) * ((1 : U ⟶ G.X) ≫ b)) := by rw [h11, mul_one]
    _ = _ := by ac_rfl


/-- Coordinate characters distinguish maps to any diagonalizable group. -/
theorem diagonalizable_hom_ext (R : CommRingCat.{u}) (Λ : Type u) [AddCommGroup Λ]
    (U : Over (Spec R)) (a b : U ⟶ (Diagonalizable.groupScheme R Λ).X)
    (h : ∀ m : Λ, a ≫ (CommGroupScheme.groupHom
        (DiagonalizableCharacter.evalCharacter R Λ m)).hom.hom =
      b ≫ (CommGroupScheme.groupHom
        (DiagonalizableCharacter.evalCharacter R Λ m)).hom.hom) : a = b := by
  apply (Diagonalizable.characterPointsEquiv R Λ U).injective
  apply MonoidHom.ext
  intro m
  simpa only [DiagonalizableCharacter.evalCharacter_apply, ofAdd_toAdd] using
    congrArg (Gm.pointsEquiv (Spec R) U) (h m.toAdd)

/-- Over an algebraically closed field, coordinate characters reduce the
pointed diagonalizable-target theorem to its multiplicative-group case. -/
theorem diagonalizable_isMonHom_algClosed (hu : UnitsProductDecompositionStatement.{u})
    (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [QuasiCompact G.X.hom] [ConnectedSpace G.X.left]
    (Λ : Type u) [AddCommGroup Λ]
    (p : G.X ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X)
    (hp : η[G.X] ≫ p = η[(Diagonalizable.groupScheme (CommRingCat.of k) Λ).X]) :
    IsMonHom p := by
  apply isMonHom_of_points p hp
  intro U x y
  apply diagonalizable_hom_ext (CommRingCat.of k) Λ U
  intro m
  let χ := CommGroupScheme.groupHom
    (DiagonalizableCharacter.evalCharacter (CommRingCat.of k) Λ m)
  have hc : η[G.X] ≫ (p ≫ χ.hom.hom) = η[(Gm (Spec (CommRingCat.of k))).X] := by
    rw [← Category.assoc, hp, IsMonHom.one_hom]
  let : IsMonHom (p ≫ χ.hom.hom) := gm_isMonHom hu k G _ hc
  change ((x * y) ≫ p) ≫ χ.hom.hom = ((x ≫ p) * (y ≫ p)) ≫ χ.hom.hom
  calc
    ((x * y) ≫ p) ≫ χ.hom.hom = (x * y) ≫ (p ≫ χ.hom.hom) := Category.assoc _ _ _
    _ = (x ≫ (p ≫ χ.hom.hom)) * (y ≫ (p ≫ χ.hom.hom)) :=
      MonObj.mul_comp x y (p ≫ χ.hom.hom)
    _ = ((x ≫ p) * (y ≫ p)) ≫ χ.hom.hom := by
      rw [MonObj.mul_comp (x ≫ p) (y ≫ p) χ.hom.hom]
      simp only [Category.assoc]

/-- Smooth connected group schemes over fields are geometrically connected,
using their unit as rational section. -/
theorem source_geometricallyConnected (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [ConnectedSpace G.X.left] : GeometricallyConnected G.X.hom :=
  Langlands.AlgebraicGeometry.geometricallyConnected_of_smooth_connected_section
    G.X.hom η[G.X].left η[G.X].w

/-- A pointed scheme map whose composite with a target group isomorphism is a
homomorphism is itself a homomorphism. -/
theorem isMonHom_of_target_iso {S : Scheme.{u}} {G H T : GroupScheme S}
    (e : H ≅ T) (p : G.X ⟶ H.X) [IsMonHom (p ≫ e.hom.hom.hom)] : IsMonHom p := by
  have he : (p ≫ e.hom.hom.hom) ≫ e.inv.hom.hom = p := by
    rw [Category.assoc]
    change p ≫ (e.hom ≫ e.inv).hom.hom = p
    simp
  rw [← he]
  infer_instance


/-- Field pullback retains every geometric hypothesis on the source. -/
theorem source_baseChange (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [QuasiCompact G.X.hom] [ConnectedSpace G.X.left] :
    Smooth ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom ∧
      QuasiCompact ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom ∧
      ConnectedSpace ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.left := by
  let : GeometricallyConnected G.X.hom := source_geometricallyConnected k G
  change Smooth (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K)) ∧
    QuasiCompact (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K)) ∧
    ConnectedSpace (CategoryTheory.Limits.pullback G.X.hom (algebraBaseMap k K) : Scheme)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Faithful field pullback and a diagonalizable base-change comparison remove
algebraic closedness from pointed diagonalizable-target rigidity. -/
theorem diagonalizable_isMonHom (hu : UnitsProductDecompositionStatement.{u})
    (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [QuasiCompact G.X.hom] [ConnectedSpace G.X.left]
    (Λ : Type u) [AddCommGroup Λ]
    (p : G.X ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X)
    (hp : η[G.X] ≫ p = η[(Diagonalizable.groupScheme (CommRingCat.of k) Λ).X]) :
    IsMonHom p := by
  let K := AlgebraicClosure k
  let b := algebraBaseMap k K
  let G' := (GroupScheme.baseChange b).obj G
  let p' := (Over.pullback b).map p
  let e := Diagonalizable.baseChangeIso b Λ
  obtain ⟨hs, hq, hc⟩ := source_baseChange k K G
  let : Smooth G'.X.hom := hs
  let : QuasiCompact G'.X.hom := hq
  let : ConnectedSpace G'.X.left := hc
  have hp' : η[G'.X] ≫ (p' ≫ e.hom.hom.hom) =
      η[(Diagonalizable.groupScheme (CommRingCat.of K) Λ).X] := by
    rw [← Category.assoc, pointed_morphism_algebraPullback K p hp, IsMonHom.one_hom]
  let : IsMonHom (p' ≫ e.hom.hom.hom) :=
    diagonalizable_isMonHom_algClosed hu K G' Λ _ hp'
  let : IsMonHom p' := isMonHom_of_target_iso (G := G') e p'
  let := GaloisCocharacterDescent.faithful_algebraPullback k K
  exact GaloisCocharacterDescent.isMonHom_of_faithfulMap (Over.pullback b) p

end PointedMapReduction


/-- The exact pointed-morphism target reduces to product-unit decomposition. -/
def MultiplicativeTypePointedMapReductionStatement : Prop :=
  UnitsProductDecompositionStatement.{u} → MultiplicativeTypePointedMapStatement.{u}

/-- Proof of the complete conditional reduction, including nonaffine sources
and arbitrary, possibly nonsmooth, groups of multiplicative type. -/
theorem multiplicativeTypePointedMap_of_unitsProductDecomposition :
    MultiplicativeTypePointedMapReductionStatement.{u} := by
  intro hu k _ G T hs hq hc hT p hp
  let := hs
  let := hq
  let := hc
  obtain ⟨K, hK, aK, Λ, hΛ, hfg, ⟨e⟩⟩ := hT
  let := hK
  let := aK
  let := hΛ
  let b := algebraBaseMap k K
  let G' := (GroupScheme.baseChange b).obj G
  let p' := (Over.pullback b).map p
  obtain ⟨hs', hq', hc'⟩ := PointedMapReduction.source_baseChange k K G
  let : Smooth G'.X.hom := hs'
  let : QuasiCompact G'.X.hom := hq'
  let : ConnectedSpace G'.X.left := hc'
  have hp' : η[G'.X] ≫ (p' ≫ e.hom.hom.hom) =
      η[(Diagonalizable.groupScheme (CommRingCat.of K) Λ).X] := by
    rw [← Category.assoc, pointed_morphism_algebraPullback K p hp, IsMonHom.one_hom]
  let : IsMonHom (p' ≫ e.hom.hom.hom) :=
    PointedMapReduction.diagonalizable_isMonHom hu K G' Λ _ hp'
  let : IsMonHom p' := PointedMapReduction.isMonHom_of_target_iso (G := G') e p'
  let := GaloisCocharacterDescent.faithful_algebraPullback k K
  let : IsMonHom p :=
    GaloisCocharacterDescent.isMonHom_of_faithfulMap (Over.pullback b) p
  exact ⟨Grp.homMk p, rfl⟩

end Langlands.GroupScheme
