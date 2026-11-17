import Langlands.GroupScheme.Reductive.AffineSplitReflectionRepresentatives
import Langlands.GroupScheme.Reductive.LocalSplitRootPairLaws
import Langlands.GroupScheme.Reductive.LocalSplitRankOneLaws

/-! # Normalized global reflection representatives for split reductive groups over rings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme

namespace AffineSplitReflection

open LocalSplitCell LocalSplitRootBaseChange

/-- A ring homomorphism sends the unit `-1` to `-1`. -/
theorem units_map_neg_one {A B : Type*} [Ring A] [Ring B] (φ : A →+* B) :
    Units.map φ.toMonoidHom (-1) = -1 := by
  ext
  simp

section SquareDescent

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]
  {G : GroupScheme (Spec (CommRingCat.of R))}

/-- The Weyl square identity `n² = ν(-1)` holds over `R` once it holds for the base-changed root
maps over the localization of `R` at every prime. -/
theorem weylPoint_mul_self_of_localizations [IsAffineHom G.X.hom]
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G} {u v : Ga R ⟶ G} (nu : I → ℤ)
    (h : ∀ (p : Ideal R) [p.IsPrime],
      weylPoint (baseChangeRoot (Localization.AtPrime p) u)
          (baseChangeRoot (Localization.AtPrime p) v) *
        weylPoint (baseChangeRoot (Localization.AtPrime p) u)
          (baseChangeRoot (Localization.AtPrime p) v) =
        cocharPoint nu (𝟙_ _) (-1) ≫
          (splitTorus.baseChangeHom (K := Localization.AtPrime p) G I i).hom.hom) :
    weylPoint u v * weylPoint u v = cocharPoint nu (𝟙_ _) (-1) ≫ i.hom.hom := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsAffine (𝟙_ (Over (Spec (CommRingCat.of R)))).left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of R)))
  apply over_hom_ext_of_localization
  intro p _ W k
  let A := Localization.AtPrime p
  let E := GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) G W
  have hk : k = toUnit _ := toUnit_unique _ _
  have h1 := congrArg (fun g => E (toUnit W ≫ g)) (h p)
  simp only at h1
  rw [MonObj.comp_mul, toUnit_comp_eq_constantPoint, map_mul,
    baseChangePointsEquiv_constantWeyl, ← Category.assoc, comp_cocharPoint,
    units_map_neg_one, baseChangePointsEquiv_torus, baseChangePointsEquiv_cocharPoint] at h1
  rw [hk, MonObj.comp_mul, toUnit_comp_eq_constantPoint, ← Category.assoc, comp_cocharPoint,
    units_map_neg_one, h1]

end SquareDescent

section Normalized

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom] {J : Type u}

/-- A family `n` of points of `G`, one for each root, is a family of *normalized reflection
representatives* when every `n a` acts on the torus by the reflection in `a` (`IsWeylPoint`)
and its square `n a * n a` is the torus point `a^∨(-1)`, the image of `-1` under the coroot
of `a`. -/
def IsNormalizedRepresentatives (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (P : RootDatum J (I → ℤ) (I → ℤ))
    (n : J → (Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X)) : Prop :=
  (∀ a, IsWeylPoint i (n a) (P.reflection a)) ∧
    ∀ a, n a * n a = cocharPoint (P.coroot a) (𝟙_ _) (-1) ≫ i.hom.hom

/-- **Normalized reflection representatives exist.** For a split reductive group over an
arbitrary ring with free root spaces, there are points `n a` of `G`, one for each root, such
that `n a` acts on the torus by the reflection in `a` and `n a * n a = a^∨(-1)`. -/
theorem exists_normalized_representatives (hG : IsReductive G)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    {P : RootDatum J (I → ℤ) (I → ℤ)} (hP : IsFibrewiseRootDatumOf I G i P)
    (hfree : ∀ α : J, Nonempty
      (splitTorus.exponentWeightSpace I G i (P.root α) ≃ₗ[CommRingCat.of R] CommRingCat.of R)) :
    ∃ n : J → (Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X),
      IsNormalizedRepresentatives i P n := by
  classical
  let := P.indexNeg
  let xs := LocalRootGroup.rootParametrizationsOfFreeWeights i hG hmax hP hfree
  have hxs := LocalRootGroup.isRootParametrization_rootParametrizationsOfFreeWeights
    i hG hmax hP hfree
  have hneg : ∀ a : J, P.root (-a) = -P.root a := fun a => by
    change P.root (P.reflectionPerm a a) = _
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
  have hm : ∀ a : J, IsRootParametrization i (-P.root a) (xs (-a)) := fun a => by
    rw [← hneg]
    exact hxs _
  have hc : ∀ a : J, ∃ c : Rˣ,
      IsWeylPoint i (weylPoint (xs a) (scaleHom (c : R) ≫ xs (-a))) (P.reflection a) :=
    fun a => by
      obtain ⟨y, t, x, hx⟩ := exists_dualFactorization hG i hmax hP a (hxs a) (hm a)
      exact exists_isWeylPoint_of_dualFactorization hG i hi hmax hP a (hxs a) (hm a) hx
  choose c hc using hc
  refine ⟨fun a => weylPoint (xs a) (scaleHom (c a : R) ≫ xs (-a)), hc, fun a => ?_⟩
  change weylPoint (xs a) (scaleHom (c a : R) ≫ xs (-a)) *
    weylPoint (xs a) (scaleHom (c a : R) ≫ xs (-a)) = _
  apply weylPoint_mul_self_of_localizations
  intro p _
  let A := Localization.AtPrime p
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap R A)).obj G).X.hom :=
    inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom (algebraBaseMap R A)))
  have hiA : IsClosedSubgroup (splitTorus.baseChangeHom (K := A) G I i) :=
    IsClosedSubgroup.iso_comp (splitTorus.baseChangeIso (algebraBaseMap R A) I).symm
      (hi.baseChange (algebraBaseMap R A))
  have hmaxA : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I)
      (splitTorus.baseChangeHom (K := A) G I i) :=
    splitTorus.isFibrewiseMaximalTorus_baseChangeHom I G i hmax
  have hL := localSplitRootPairLaws A ((GroupScheme.baseChange (algebraBaseMap R A)).obj G)
    (hG.baseChange (algebraBaseMap R A)) I (splitTorus.baseChangeHom (K := A) G I i) hiA hmaxA
    J P (hP.baseChange_implicit (A := A)) a (baseChangeRoot A (xs a))
    (baseChangeRoot A (scaleHom (c a : R) ≫ xs (-a)))
    (isRootParametrization_baseChangeRoot A i _ _ (hxs a))
    (isRootParametrization_baseChangeRoot A i _ _ ((hm a).scale (c a)))
    (isWeylPoint_baseChange A (hc a))
  have h := hL.2.2.1 (𝟙_ _)
  rwa [← toUnit_comp_eq_constantPoint,
    toUnit_unique (toUnit (𝟙_ (Over (Spec (CommRingCat.of A))))) (𝟙 _),
    Category.id_comp] at h

omit [DecidableEq I] in
/-- The torus point `ν(-1)` squares to one. -/
theorem cocharPoint_neg_one_mul_self (ν : I → ℤ) (Z : Over (Spec (CommRingCat.of R))) :
    cocharPoint ν Z (-1) * cocharPoint ν Z (-1) = 1 := by
  apply (splitTorus.pointsEquiv I Z).injective
  rw [map_mul, map_one]
  simp only [cocharPoint, MulEquiv.apply_symm_apply]
  funext j
  simp [← mul_zpow]

/-- **Reflection representatives, in the form used for clause 4.** There are points `n a`, one
for each root, such that `n a` induces the reflection `Equiv.reflection P a` (the body of the
statement's `Induces` relation, spelled out) and `n a * n a` is a torus point of order at most
two. -/
theorem exists_reflection_representatives (hG : IsReductive G)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    {P : RootDatum J (I → ℤ) (I → ℤ)} (hP : IsFibrewiseRootDatumOf I G i P)
    (hfree : ∀ α : J, Nonempty
      (splitTorus.exponentWeightSpace I G i (P.root α) ≃ₗ[CommRingCat.of R] CommRingCat.of R)) :
    ∃ n : J → (Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X),
      (∀ a, ∃ σ : splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I ≅
          splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I,
        IsNormalizingPoint (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i
            (n a) σ ∧
          ∀ (U : Over (Spec (CommRingCat.of R)))
            (x : U ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) (m : I → ℤ),
            ∏ j, splitTorus.pointsEquiv I U
                (x ≫ (CommGroupScheme.groupHom σ.hom).hom.hom) j ^ m j =
              ∏ j, splitTorus.pointsEquiv I U x j ^ (RootPairing.Equiv.reflection P a • m) j) ∧
      ∀ a, ∃ t : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X,
        t * t = 1 ∧ n a * n a = t ≫ i.hom.hom := by
  obtain ⟨n, hw, hsq⟩ := exists_normalized_representatives hG i hi hmax hP hfree
  refine ⟨n, fun a => ⟨splitTorus.exponentCommIso _ I (P.reflection a),
    (hw a).isNormalizingPoint, fun U z m => ?_⟩, fun a =>
      ⟨cocharPoint (P.coroot a) (𝟙_ _) (-1), cocharPoint_neg_one_mul_self _ _, hsq a⟩⟩
  rw [prod_pointsEquiv_exponentCommIso]
  rfl

end Normalized

end AffineSplitReflection

end Langlands.GroupScheme
