import Langlands.GroupScheme.Reductive.AffinePinnedFixedRigidity
import Langlands.GroupScheme.Reductive.AffinePinnedCoefficientTests

/-! # Fixed pinned comparison existence on arbitrary common schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.AffinePinnedModel

variable {M N : AffinePinnedModel.{u}}
  (θ : RootPairing.Equiv N.rootDatum M.rootDatum)
  (hθ : ∀ s : N.rootIndex, s ∈ N.basis.support ↔ θ.indexEquiv s ∈ M.basis.support)

/-- The all-test monomial character formula determines the whole actual
coordinate torus isomorphism, over any base. -/
theorem torusIso_eq_fixedTorusIso_of_characters {T : Scheme.{u}}
    (τ : splitTorus T M.coordinates ≅ splitTorus T N.coordinates)
    (hτ : ∀ (U : Over T) (x : U ⟶ (splitTorus T M.coordinates).X) (m : N.coordinates → ℤ),
      ∏ j, splitTorus.pointsEquiv N.coordinates U (x ≫ τ.hom.hom.hom) j ^ m j =
        ∏ i, splitTorus.pointsEquiv M.coordinates U x i ^ θ.weightMap m i) :
    τ = fixedTorusIso θ T := by
  classical
  apply Iso.ext
  apply hom_ext_points
  intro U x
  apply (splitTorus.pointsEquiv N.coordinates U).injective
  funext j
  have h := (hτ U x (Pi.single j 1)).trans
    (fixedTorusIso_characters θ T U x (Pi.single j 1)).symm
  simpa [Pi.single_apply] using h

local instance scalarAffineExistence (P : AffinePinnedModel.{u})
    (A : Type u) [CommRing A] [Algebra P.ring A] :
    IsAffineHom (P.groupOver (algebraBaseMap P.ring A)).X.hom :=
  (P.reductive.baseChange (algebraBaseMap P.ring A)).isAffineHom

variable (A : Type u) [CommRing A] [Algebra M.ring A] [Algebra N.ring A]

/-- The base-ring differential equations in the affine pinned theorem imply
the fixed actual pinning-point equations on every affine coefficient test. -/
theorem IsAffineSolution.preservesFixedPinning
    {e : Comparison (algebraBaseMap M.ring A) (algebraBaseMap N.ring A)}
    (he : IsAffineSolution θ hθ A e) : PreservesFixedPinning θ hθ e := by
  intro B _ _ _ a ha hb s
  have hv := congrArg
    (fun z : Additive (lieKernel (N.groupOver (algebraBaseMap N.ring A)) A) => z.toMul.val.left)
    (he.2 s)
  change (((M.scalarExtension A).pinning (fixedSimpleEquiv θ hθ s) 1).val.toMul.val).left ≫
      e.hom.hom.hom.left =
    (((N.scalarExtension A).pinning s 1).val.toMul.val).left at hv
  rw [scalarExtension_pinning_point, scalarExtension_pinning_point] at hv
  have hm := M.rootVectorPoint_coefficient (algebraBaseMap M.ring A) A B (𝟙 _) a
    (by simp) (by simpa only [Category.comp_id] using ha) (fixedSimpleEquiv θ hθ s)
  have hn := N.rootVectorPoint_coefficient (algebraBaseMap N.ring A) A B (𝟙 _) a
    (by simp) (by simpa only [Category.comp_id] using hb) s
  simp only [Category.comp_id] at hm hn
  rw [← hm, Category.assoc, hv]
  exact hn

/-- An exact affine pinned solution has the fixed full torus and all-affine
pinning predicates. -/
theorem IsAffineSolution.fixed
    {e : Comparison (algebraBaseMap M.ring A) (algebraBaseMap N.ring A)}
    (he : IsAffineSolution θ hθ A e) :
    PreservesFixedTorus θ e ∧ PreservesFixedPinning θ hθ e := by
  obtain ⟨τ, hsquare, hchars⟩ := he.1
  have hτ := torusIso_eq_fixedTorusIso_of_characters θ τ hchars
  refine ⟨?_, he.preservesFixedPinning θ hθ A⟩
  change M.inclusionOver (algebraBaseMap M.ring A) ≫ e.hom = _
  change M.inclusionOver (algebraBaseMap M.ring A) ≫ e.hom =
    τ.hom ≫ N.inclusionOver (algebraBaseMap N.ring A) at hsquare
  rw [hτ] at hsquare
  exact hsquare

/-- An actual fixed pinned comparison over every common coefficient spectrum,
from the supplied exact affine pinned theorem. -/
def fixedAffineComparison (hAffine : AffinePinnedIsomorphismTheoremStatement.{u}) :
    FixedComparison θ hθ (algebraBaseMap M.ring A) (algebraBaseMap N.ring A) :=
  ⟨affineSolution θ hθ A hAffine,
    (affineSolution_spec θ hθ A hAffine).fixed θ hθ A⟩

variable {T W : Scheme.{u}}

/-- The factorization through global functions for a morphism to a model's
affine base; the common source scheme need not be affine. -/
theorem toSpecΓ_factor (P : AffinePinnedModel.{u}) (f : T ⟶ P.base) :
    T.toSpecΓ ≫ (Spec.map f.appTop ≫ P.base.isoSpec.inv) = f := by
  rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]

/-- Every common scheme admits a fixed pinned comparison, using its
canonical affinization and the exact affine full-faithfulness input. -/
theorem fixedComparison_nonempty
    (hAffine : AffinePinnedIsomorphismTheoremStatement.{u})
    (f : T ⟶ M.base) (g : T ⟶ N.base) : Nonempty (FixedComparison θ hθ f g) := by
  let A := Γ(T, ⊤)
  let f₀ : Spec A ⟶ M.base := Spec.map f.appTop ≫ M.base.isoSpec.inv
  let g₀ : Spec A ⟶ N.base := Spec.map g.appTop ≫ N.base.isoSpec.inv
  let : Algebra M.ring A := (Spec.preimage f₀).hom.toAlgebra
  let : Algebra N.ring A := (Spec.preimage g₀).hom.toAlgebra
  have hf₀ : algebraBaseMap M.ring A = f₀ := Spec.map_preimage _
  have hg₀ : algebraBaseMap N.ring A = g₀ := Spec.map_preimage _
  have hf : T.toSpecΓ ≫ algebraBaseMap M.ring A = f := by
    rw [hf₀]
    exact toSpecΓ_factor M f
  have hg : T.toSpecΓ ≫ algebraBaseMap N.ring A = g := by
    rw [hg₀]
    exact toSpecΓ_factor N g
  exact ⟨(fixedAffineComparison θ hθ A hAffine).pullAlong θ hθ T.toSpecΓ hf hg⟩

/-- The canonical fixed pinned comparison on an arbitrary common scheme. -/
def fixedComparison (hAffine : AffinePinnedIsomorphismTheoremStatement.{u})
    (f : T ⟶ M.base) (g : T ⟶ N.base) : FixedComparison θ hθ f g :=
  Classical.choice (fixedComparison_nonempty θ hθ hAffine f g)

/-- The fixed comparison is unique on the whole arbitrary common scheme. -/
theorem fixedComparison_unique (hAffine : AffinePinnedIsomorphismTheoremStatement.{u})
    (f : T ⟶ M.base) (g : T ⟶ N.base) (e : FixedComparison θ hθ f g) :
    e.val = (fixedComparison θ hθ hAffine f g).val :=
  FixedComparison.eq_of_affineTheorem_scheme θ hθ hAffine _ _

/-- Canonical fixed comparisons commute with arbitrary common-base pullback. -/
theorem fixedComparison_pull (hAffine : AffinePinnedIsomorphismTheoremStatement.{u})
    (f : T ⟶ M.base) (g : T ⟶ N.base) (q : W ⟶ T) :
    pullComparison (fixedComparison θ hθ hAffine f g).val q =
      (fixedComparison θ hθ hAffine (q ≫ f) (q ≫ g)).val :=
  FixedComparison.eq_of_affineTheorem_scheme θ hθ hAffine
    ((fixedComparison θ hθ hAffine f g).pull θ hθ q) _

end Langlands.GroupScheme.AffinePinnedModel
