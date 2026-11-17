import Langlands.GroupScheme.Reductive.AffineSplitSurjectionLocalCore
import Langlands.GroupScheme.Reductive.SplitDataBaseChange
import Langlands.GroupScheme.Reductive.GlobalSplitRootParametrization
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.Torus.SplitTorusCharacterIdempotents

/-! # Vanishing of the characteristic exponent after base change to local algebras -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffineSplitSurjection

open LocalSplitCell LocalSplitRootBaseChange

variable {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  {I I' : Type u} [Fintype I] [Fintype I']

/-- The base change to `A` of a homomorphism of split tori, as a homomorphism of the
coordinate split tori over `A`. -/
def torusBaseChange
    (τ : splitTorus (Spec (CommRingCat.of R)) I ⟶ splitTorus (Spec (CommRingCat.of R)) I') :
    splitTorus.commGroupScheme (Spec (CommRingCat.of A)) I ⟶
      splitTorus.commGroupScheme (Spec (CommRingCat.of A)) I' :=
  show splitTorus (Spec (CommRingCat.of A)) I ⟶ splitTorus (Spec (CommRingCat.of A)) I' from
    (splitTorus.baseChangeIso (algebraBaseMap R A) I).inv ≫
      (GroupScheme.baseChange (algebraBaseMap R A)).map τ ≫
        (splitTorus.baseChangeIso (algebraBaseMap R A) I').hom

theorem groupHom_torusBaseChange
    (τ : splitTorus (Spec (CommRingCat.of R)) I ⟶ splitTorus (Spec (CommRingCat.of R)) I') :
    CommGroupScheme.groupHom (torusBaseChange A τ) =
      (splitTorus.baseChangeIso (algebraBaseMap R A) I).inv ≫
        (GroupScheme.baseChange (algebraBaseMap R A)).map τ ≫
          (splitTorus.baseChangeIso (algebraBaseMap R A) I').hom :=
  rfl

/-- Torus points of the base-changed torus map correspond to torus points of the original
map. -/
theorem baseChangePointsEquiv_torusBaseChange
    (τ : splitTorus (Spec (CommRingCat.of R)) I ⟶ splitTorus (Spec (CommRingCat.of R)) I')
    {Z : Over (Spec (CommRingCat.of A))}
    (t : Z ⟶ (splitTorus (Spec (CommRingCat.of A)) I).X) :
    GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) (splitTorus _ I') Z
        ((t ≫ (CommGroupScheme.groupHom (torusBaseChange A τ)).hom.hom) ≫
          (splitTorus.baseChangeIso (algebraBaseMap R A) I').inv.hom.hom) =
      GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) (splitTorus _ I) Z
          (t ≫ (splitTorus.baseChangeIso (algebraBaseMap R A) I).inv.hom.hom) ≫ τ.hom.hom := by
  rw [← GroupScheme.baseChangePointsEquiv_comp, groupHom_torusBaseChange]
  congr 1
  simp only [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id, Category.comp_id]

/-- The value of a character on a point over a test scheme `Z` is the value on the same
point regarded over the original base. -/
private theorem charValue_eq_coe_prod (m : I → ℤ) {Z : Over (Spec (CommRingCat.of R))}
    (x : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) :
    VectorGroup.charValue (S := splitTorus.commGroupScheme _ I)
        (splitTorus.exponentCharacter _ I m) Z x =
      ((∏ j, splitTorus.pointsEquiv I Z x j ^ m j : (Γ(Z.left, ⊤))ˣ) : Γ(Z.left, ⊤)) := by
  rw [VectorGroup.charValue, splitTorus.pointsEquiv_exponentCharacter]

/-- A character map on an open set `V` gives the identity of exponent characters after
base change to any algebra whose spectrum maps into `V`. -/
theorem torusBaseChange_exponentCharacter
    {τ : splitTorus (Spec (CommRingCat.of R)) I ⟶ splitTorus (Spec (CommRingCat.of R)) I'}
    {V : (Spec (CommRingCat.of R)).Opens} {h : (I' → ℤ) →ₗ[ℤ] (I → ℤ)}
    (hV : splitTorus.CharacterMapOn τ V h) (hA : algebraBaseMap R A ⁻¹ᵁ V = ⊤)
    (m : I' → ℤ) :
    torusBaseChange A τ ≫ splitTorus.exponentCharacter _ I' m =
      splitTorus.exponentCharacter _ I (h m) := by
  apply CommGroupScheme.hom_ext_points
  intro Z t
  apply (Gm.pointsEquiv _ Z).injective
  apply Units.ext
  change VectorGroup.charValue (S := splitTorus.commGroupScheme _ I')
      (splitTorus.exponentCharacter _ I' m) Z
        (t ≫ (CommGroupScheme.groupHom (torusBaseChange A τ)).hom.hom) =
    VectorGroup.charValue (S := splitTorus.commGroupScheme _ I)
      (splitTorus.exponentCharacter _ I (h m)) Z t
  rw [charValue_exponentCharacter_baseChange (R := R) A,
    charValue_exponentCharacter_baseChange (R := R) A,
    baseChangePointsEquiv_torusBaseChange, charValue_eq_coe_prod, charValue_eq_coe_prod]
  congr 1
  apply hV
  change (Z.hom ≫ algebraBaseMap R A) ⁻¹ᵁ V = ⊤
  rw [Scheme.Hom.comp_preimage, hA, Scheme.Hom.preimage_top]

section Local

variable [DecidableEq I] [DecidableEq I']

local instance affineBaseChange (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom] :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap R A)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap R A)))

/-- Base change preserves local quasi-finiteness of a homomorphism of group schemes. -/
theorem locallyQuasiFinite_baseChange_map {G H : GroupScheme (Spec (CommRingCat.of R))}
    (φ : G ⟶ H) [LocallyQuasiFinite φ.hom.hom.left] :
    LocallyQuasiFinite ((GroupScheme.baseChange (algebraBaseMap R A)).map φ).hom.hom.left :=
  MorphismProperty.of_isPullback (baseChange_map_isPullback (algebraBaseMap R A) φ).flip
    inferInstance

omit [DecidableEq I] [DecidableEq I'] in
/-- The base change of the torus square `i ≫ φ = τ ≫ i'` to `A`. -/
theorem baseChangeHom_comp_map {G H : GroupScheme (Spec (CommRingCat.of R))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] [Smooth G.X.hom] [Smooth H.X.hom]
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H}
    {φ : G ⟶ H}
    {τ : splitTorus (Spec (CommRingCat.of R)) I ⟶ splitTorus (Spec (CommRingCat.of R)) I'}
    (hsq : i ≫ φ = τ ≫ i') :
    splitTorus.baseChangeHom (K := A) G I i ≫ (GroupScheme.baseChange (algebraBaseMap R A)).map φ =
      CommGroupScheme.groupHom (torusBaseChange A τ) ≫ splitTorus.baseChangeHom (K := A) H I' i' := by
  rw [groupHom_torusBaseChange]
  simp only [splitTorus.baseChangeHom, Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp,
    hsq]

/-- **Vanishing of the characteristic exponent over local algebras.** Suppose that the torus
map `τ` acts on characters through the weight map of a root-datum isogeny `r` on an open set
`V`. Then for every local `R`-algebra `A` whose spectrum maps into `V`, if some root factor of
`r` differs from `1`, the characteristic exponent of `r` vanishes in `A`. -/
theorem natCast_eq_zero_of_local_baseChange [IsLocalRing A]
    {G H : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (hG : IsReductive G) (hH : IsReductive H)
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H}
    {J J' : Type u} [Finite J] [Finite J']
    {P : RootDatum J (I → ℤ) (I → ℤ)} {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
    [P.IsReduced] [Q.IsReduced]
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P)
    (hrootG : ∀ α : J, Nonempty
      (splitTorus.exponentWeightSpace I G i (P.root α) ≃ₗ[CommRingCat.of R] CommRingCat.of R))
    (hmax' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') i')
    (hQ : IsFibrewiseRootDatumOf I' H i' Q)
    (hrootH : ∀ α : J', Nonempty
      (splitTorus.exponentWeightSpace I' H i' (Q.root α) ≃ₗ[CommRingCat.of R] CommRingCat.of R))
    {φ : G ⟶ H}
    {τ : splitTorus (Spec (CommRingCat.of R)) I ⟶ splitTorus (Spec (CommRingCat.of R)) I'}
    [LocallyQuasiFinite φ.hom.hom.left] (hsq : i ≫ φ = τ ≫ i')
    {V : (Spec (CommRingCat.of R)).Opens} {h : (I' → ℤ) →ₗ[ℤ] (I → ℤ)}
    (hV : splitTorus.CharacterMapOn τ V h)
    {p : ℕ} (r : Langlands.LinearAlgebra.RootDatumIsogeny p Q P) (hr : r.weightMap = h)
    (hA : algebraBaseMap R A ⁻¹ᵁ V = ⊤) (β : J') (hβ : r.rootFactor β ≠ 1) :
    (p : A) = 0 := by
  let : Smooth G.X.hom := hG.smooth
  let : Smooth H.X.hom := hH.smooth
  let : LocallyQuasiFinite ((GroupScheme.baseChange (algebraBaseMap R A)).map φ).hom.hom.left :=
    locallyQuasiFinite_baseChange_map A φ
  have hweight : ∀ m : I' → ℤ, torusBaseChange A τ ≫ splitTorus.exponentCharacter _ I' m =
      splitTorus.exponentCharacter _ I (r.weightMap m) := by
    intro m
    rw [torusBaseChange_exponentCharacter A hV hA, hr]
  exact RelativeIsogeny.natCast_eq_zero_of_rootFactor_ne_one
    (splitTorus.baseChangeHom (K := A) G I i) (splitTorus.baseChangeHom (K := A) H I' i')
    (IsFibrewiseRootDatumOf.baseChange (A := A) G I i hP)
    (IsFibrewiseRootDatumOf.baseChange (A := A) H I' i' hQ)
    r (torusBaseChange A τ) hweight ((GroupScheme.baseChange (algebraBaseMap R A)).map φ)
    (baseChangeHom_comp_map A hsq) (hH.baseChange (algebraBaseMap R A))
    (IsFibrewiseMaximalTorus.baseChange_coordinates hmax' (algebraBaseMap R A)) β
    (isRootParametrization_baseChangeRoot A i _ _
      (LocalRootGroup.isRootParametrization_rootParametrizationsOfFreeWeights i hG hmax hP hrootG
        (r.indexEquiv β)))
    (isRootParametrization_baseChangeRoot A i' _ _
      (LocalRootGroup.isRootParametrization_rootParametrizationsOfFreeWeights i' hH hmax' hQ hrootH
        β))
    hβ

end Local

end Langlands.GroupScheme.AffineSplitSurjection
