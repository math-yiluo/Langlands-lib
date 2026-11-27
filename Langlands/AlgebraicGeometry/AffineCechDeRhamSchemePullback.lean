import Langlands.AlgebraicGeometry.AffineCechDeRhamSquareZeroPullback
import Langlands.AlgebraicGeometry.CechPullback

/-! # Degree-one affine Čech–de Rham pullback of a scheme morphism -/

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq (inter inter_le_comp)

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.AffineCechDeRham

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of R)} {g : Y ⟶ Spec (CommRingCat.of R)}
  {U : Scheme.AffineOpenCover.{u} X} {V : Scheme.AffineOpenCover.{u} Y}

/-- The map on section algebras of opens compatible with a morphism over the base. -/
def pullbackSections (γ : X ⟶ Y) (hγ : γ ≫ g = f)
    {W : X.Opens} {Z : Y.Opens} (hW : W ≤ γ ⁻¹ᵁ Z) :
    (sectionAlgebras g).obj (op Z) →ₐ[R] (sectionAlgebras f).obj (op W) :=
  { (γ.appLE Z W hW).hom with
    commutes' := fun r => by
      change (g.appLE ⊤ Z le_top ≫ γ.appLE Z W hW).hom
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) =
        (f.appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)
      rw [Scheme.Hom.appLE_comp_appLE, hγ] }

variable (I : Ideal R) (γ : X ⟶ Y) (hγ : γ ≫ g = f)
  (β : U.I₀ → V.I₀) (hβ : ∀ i, coverOpens U i ≤ γ ⁻¹ᵁ coverOpens V (β i))

/-- An actual global morphism gives a local pullback system whose maps on an
intersection are independent of the selected vertex. -/
def LocalPullbacks.ofMorphism : LocalPullbacks (f := f) (g := g) I β where
  sections τ _ := pullbackSections γ hγ
    (Langlands.Cohomology.Cech.inter_le_preimage γ hβ τ)
  restrict_sections := by
    intro p q τ θ i
    ext a
    change (γ.appLE _ _ _ ≫ X.presheaf.map (homOfLE (inter_le_comp τ θ)).op).hom a =
      (Y.presheaf.map (homOfLE (inter_le_comp (β ∘ τ) θ)).op ≫ γ.appLE _ _ _).hom a
    rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
    rfl
  congruent := by
    intro p τ i j a
    change pullbackSections γ hγ _ a - pullbackSections γ hγ _ a ∈ _
    rw [sub_self]
    exact Ideal.zero_mem _

variable [Smooth f] [IsSeparated f] [Finite U.I₀] [Smooth g] [IsSeparated g] [Finite V.I₀]

/-- Pullback along an actual global morphism on the Čech–de Rham module
of the supplied compatible covers. -/
def schemePullbackH1 : H1 g V →ₗ[R] H1 f U :=
  (LocalPullbacks.ofMorphism (⊥ : Ideal R) γ hγ β hβ).pullbackH1 (by rw [Ideal.bot_mul])

/-- The degree-one pullback of a global morphism preserves the first Hodge step. -/
theorem schemePullbackH1_maps_hodgeF1 {x : H1 g V} (hx : x ∈ hodgeF1 g V) :
    schemePullbackH1 γ hγ β hβ x ∈ hodgeF1 f U :=
  (LocalPullbacks.ofMorphism (⊥ : Ideal R) γ hγ β hβ).pullbackH1_maps_hodgeF1
    (by rw [Ideal.bot_mul]) (fun _ => rfl) hx

end Langlands.AlgebraicGeometry.AffineCechDeRham
