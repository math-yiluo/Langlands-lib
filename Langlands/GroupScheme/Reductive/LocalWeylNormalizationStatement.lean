import Langlands.GroupScheme.Reductive.LocalSplitBigCellProof
import Langlands.GroupScheme.Reductive.SplitRankOneRootCellUniversal

/-! # Weyl normalization of opposite root groups: rescaling and statements -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LocalSplitCell

/-! ### Rescaling the additive group over a ring -/

section Scale

variable {R : Type u} [CommRing R]

/-- The structure map `R → Γ(Z, 𝒪_Z)` of a scheme over `Spec R`. -/
def baseScalar (Z : Over (Spec (CommRingCat.of R))) : R →+* Γ(Z.left, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ Z.hom.appTop).hom

theorem appTop_baseScalar {Z W : Over (Spec (CommRingCat.of R))} (f : W ⟶ Z) (d : R) :
    f.left.appTop (baseScalar Z d) = baseScalar W d := by
  rw [baseScalar, baseScalar, ← Over.w f]
  rfl

/-- The coordinate of a point of `𝔾ₐ` over `Spec R`. -/
abbrev gaCoord {Z : Over (Spec (CommRingCat.of R))} (a : Z ⟶ (Ga R).X) : Γ(Z.left, ⊤) :=
  (VectorGroup.coordinates (CommRingCat.of R) 1 Z a).toAdd 0

/-- Multiplication by `d` on the points of `𝔾ₐ` over `Z`. -/
def scalePoints (d : R) (Z : Over (Spec (CommRingCat.of R))) :
    (Z ⟶ (Ga R).X) →* (Z ⟶ (Ga R).X) where
  toFun a := VectorGroup.scalarPoint _ Z (baseScalar Z d * gaCoord a)
  map_one' := by
    apply VectorGroup.points_ext
    intro j
    simp only [VectorGroup.coordinates_scalarPoint, gaCoord, map_one, toAdd_one, Pi.zero_apply,
      mul_zero]
  map_mul' a b := by
    apply VectorGroup.points_ext
    intro j
    simp only [VectorGroup.coordinates_mul, Pi.add_apply, VectorGroup.coordinates_scalarPoint,
      gaCoord, mul_add]

theorem scalePoints_naturality (d : R) {Z W : Over (Spec (CommRingCat.of R))} (f : W ⟶ Z)
    (a : Z ⟶ (Ga R).X) : scalePoints d W (f ≫ a) = f ≫ scalePoints d Z a := by
  change VectorGroup.scalarPoint _ W _ = f ≫ VectorGroup.scalarPoint _ Z _
  rw [VectorGroup.scalarPoint_comp, map_mul, appTop_baseScalar, gaCoord, gaCoord,
    VectorGroup.coordinates_comp]

/-- The endomorphism `x ↦ d x` of `𝔾ₐ` over `Spec R`. -/
def scaleHom (d : R) : Ga R ⟶ Ga R :=
  homOfPoints (scalePoints d) (scalePoints_naturality d)

theorem comp_scaleHom (d : R) {Z : Over (Spec (CommRingCat.of R))} (a : Z ⟶ (Ga R).X) :
    a ≫ (scaleHom d).hom.hom = VectorGroup.scalarPoint _ Z (baseScalar Z d * gaCoord a) :=
  comp_homOfPoints _ _ Z a

/-- The values of a rescaled root map. -/
theorem rootPoint_scaleHom {G : GroupScheme (Spec (CommRingCat.of R))} (d : R) (v : Ga R ⟶ G)
    (Z : Over (Spec (CommRingCat.of R))) (c : Γ(Z.left, ⊤)) :
    rootPoint (scaleHom d ≫ v) Z c = rootPoint v Z (baseScalar Z d * c) := by
  rw [rootPoint, Grp.comp_hom_hom, ← Category.assoc, comp_scaleHom, gaCoord,
    VectorGroup.coordinates_scalarPoint, rootPoint]

/-- Maps out of `𝔾ₐ` agree when all their values agree. -/
theorem hom_ext_rootPoint {G : GroupScheme (Spec (CommRingCat.of R))} {f g : Ga R ⟶ G}
    (h : ∀ (Z : Over (Spec (CommRingCat.of R))) (c : Γ(Z.left, ⊤)),
      rootPoint f Z c = rootPoint g Z c) : f = g := by
  apply hom_ext_points
  intro Z a
  rw [← VectorGroup.scalarPoint_coordinate _ a]
  exact h Z _

theorem scaleHom_comp_scaleHom (d e : R) : scaleHom d ≫ scaleHom e = scaleHom (e * d) := by
  apply hom_ext_points
  intro Z a
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_scaleHom, comp_scaleHom, comp_scaleHom, gaCoord,
    VectorGroup.coordinates_scalarPoint, map_mul, mul_assoc]

theorem scaleHom_one : scaleHom (1 : R) = 𝟙 (Ga R) := by
  apply hom_ext_points
  intro Z a
  rw [comp_scaleHom, map_one, one_mul, Grp.id_hom_hom, Category.comp_id,
    VectorGroup.scalarPoint_coordinate]

/-- Rescaling by a unit is an automorphism of `𝔾ₐ`. -/
def scaleIso (c : Rˣ) : Ga R ≅ Ga R where
  hom := scaleHom (c : R)
  inv := scaleHom (↑c⁻¹ : R)
  hom_inv_id := by rw [scaleHom_comp_scaleHom, Units.inv_mul, scaleHom_one]
  inv_hom_id := by rw [scaleHom_comp_scaleHom, Units.mul_inv, scaleHom_one]

instance (c : Rˣ) : IsIso (scaleHom (c : R)).hom.hom :=
  ⟨⟨(scaleIso c).inv.hom.hom, congrArg (fun f => f.hom.hom) (scaleIso c).hom_inv_id,
    congrArg (fun f => f.hom.hom) (scaleIso c).inv_hom_id⟩⟩

variable {I : Type u} [Fintype I] {G : GroupScheme (Spec (CommRingCat.of R))}

/-- Rescaling a root parametrization by a unit gives a root parametrization. -/
theorem IsRootParametrization.scale {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {m : I → ℤ} {v : Ga R ⟶ G} (hv : IsRootParametrization i m v) (c : Rˣ) :
    IsRootParametrization i m (scaleHom (c : R) ≫ v) where
  represents := by
    refine ⟨?_, ?_⟩
    · have : Mono v.hom.hom := hv.represents.1
      rw [Grp.comp_hom_hom]
      infer_instance
    · rw [show scaleHom (c : R) = (scaleIso c).hom from rfl, SubgroupFunctor.range_iso_comp]
      exact hv.represents.2
  isClosedSubgroup := by
    have : IsClosedImmersion v.hom.hom.left := hv.isClosedSubgroup
    have : IsIso (scaleHom (c : R)).hom.hom.left :=
      inferInstanceAs (IsIso ((Over.forget _).map (scaleHom (c : R)).hom.hom))
    change IsClosedImmersion ((scaleHom (c : R)).hom.hom ≫ v.hom.hom).left
    rw [Over.comp_left]
    infer_instance
  equivariant Z t x := by
    rw [rootPoint_scaleHom, rootPoint_scaleHom, hv.equivariant, mul_left_comm]

end Scale

/-! ### Rescaling and base change to a field -/

section BaseChange

variable {R : Type u} [CommRing R] (k : Type u) [Field k] [Algebra R k]

theorem baseScalar_map (Z : Over (Spec (CommRingCat.of k))) (d : R) :
    baseScalar ((Over.map (algebraBaseMap R k)).obj Z) d = baseScalar Z (algebraMap R k d) := by
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Z.hom ≫ algebraBaseMap R k).appTop).hom d =
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Z.hom.appTop).hom (algebraMap R k d)
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

variable {G : GroupScheme (Spec (CommRingCat.of R))}

/-- Base change to a field commutes with rescaling. -/
theorem baseChangeRoot_scaleHom (d : R) (v : Ga R ⟶ G) :
    LocalSplitBigCell.baseChangeRoot k (scaleHom d ≫ v) =
      scaleHom (algebraMap R k d) ≫ LocalSplitBigCell.baseChangeRoot k v := by
  apply hom_ext_rootPoint
  intro Z c
  apply (GroupScheme.baseChangePointsEquiv (algebraBaseMap R k) G Z).injective
  rw [LocalSplitBigCell.baseChangePointsEquiv_rootPoint, rootPoint_scaleHom, rootPoint_scaleHom,
    LocalSplitBigCell.baseChangePointsEquiv_rootPoint, baseScalar_map]

end BaseChange

/-! ### The two normalization statements -/

open LocalSplitBigCell in
/-- **Weyl normalization on field fibres.** Let `u` and `v` parametrize the root groups of a
root `a` and of its negative `-a = P.reflectionPerm a a` over `Spec R`. Over every field `k`
with an `R`-algebra structure, some nonzero rescaling `d` of the base change of `v` satisfies,
together with the base change of `u`, the rank-one relation
`u(X) v'(Y) = v'(Y/w) a^∨(w) u(X/w)` with `w = 1 + XY` on every test scheme, where
`v' = v ∘ (y ↦ d y)`, and `v'(-1) u(1) v'(-1)` normalizes the torus, acting through the
reflection `s_a`. -/
def FieldWeylNormalizationStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom],
    IsReductive G →
    ∀ (I : Type u) [Fintype I] [DecidableEq I] (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G),
      IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i →
    ∀ (J : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)), IsFibrewiseRootDatumOf I G i P →
    ∀ (a : J) (u v : Ga R ⟶ G), IsRootParametrization i (P.root a) u →
      IsRootParametrization i (P.root (P.reflectionPerm a a)) v →
    ∀ (k : Type u) [Field k] [Algebra R k], ∃ d : k, d ≠ 0 ∧
      (∀ Z : Over (Spec (CommRingCat.of k)),
        RootCell.RelationOver (T := splitTorus.commGroupScheme _ I)
          (splitTorus.baseChangeHom (K := k) G I i)
          (splitTorus.exponentCocharacter _ I (P.coroot a)) (baseChangeRoot k u)
          (scaleHom d ≫ baseChangeRoot k v) Z) ∧
      IsWeylPoint (splitTorus.baseChangeHom (K := k) G I i)
        (weylPoint (baseChangeRoot k u) (scaleHom d ≫ baseChangeRoot k v)) (P.reflection a)

/-- **Weyl normalization over a reduced local ring.** In the setting of
`LocalSplitRootGroupStatement`, for every simple root `a` of a base `b` and every
parametrization `u` of the root group of `a`, some parametrization `v` of the root group of
`-a = P.reflectionPerm a a` makes the Weyl point `v(-1) u(1) v(-1)` act on the torus through the
simple reflection `s_a`. -/
def LocalWeylNormalizationStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsReduced R]
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom], IsReductive G →
    ∀ (I : Type u) [Fintype I] [DecidableEq I] (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G),
      IsClosedSubgroup i → IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i →
    ∀ (J : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)), IsFibrewiseRootDatumOf I G i P →
    ∀ (b : P.Base), ∀ a ∈ b.support, ∀ u : Ga R ⟶ G, IsRootParametrization i (P.root a) u →
      ∃ v : Ga R ⟶ G, IsRootParametrization i (P.root (P.reflectionPerm a a)) v ∧
        IsWeylPoint i (weylPoint u v) (P.reflection a)

end Langlands.GroupScheme.LocalSplitCell
