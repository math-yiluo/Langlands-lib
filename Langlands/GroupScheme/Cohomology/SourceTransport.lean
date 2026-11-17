import Langlands.GroupScheme.Cohomology.DiagonalizableModuleAveraging
import Langlands.GroupScheme.Torus.AffineRelativeDiagonalizable

/-! # Pulling regular cochains along actual group-scheme homomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cohomology

variable {R : CommRingCat.{u}} {H G : GroupScheme (Spec R)}
variable {M : Type u} [AddCommGroup M] [Module R M]

theorem affinePointsTarget_natural (f : H ⟶ G) {A B : CommAlgCat.{u} R}
    (a : A ⟶ B) (h : H.affinePoints A) :
    G.affinePointMap a (H.affinePointsTarget f A h) =
      H.affinePointsTarget f B (H.affinePointMap a h) := by
  exact congrArg (fun p : H.affinePoints A →* G.affinePoints B => p h)
    (H.affinePointsTarget_naturality f a)

/-- Restrict a natural module action along an actual group-scheme homomorphism. -/
def ModuleRepresentation.precomp (ρ : ModuleRepresentation M G) (f : H ⟶ G) :
    ModuleRepresentation M H where
  action A := (ρ.action A).comp (H.affinePointsTarget f A)
  naturality a h m := by
    change modulePointMap M a (ρ.action _ (H.affinePointsTarget f _ h) m) =
      ρ.action _ (H.affinePointsTarget f _ (H.affinePointMap a h)) (modulePointMap M a m)
    rw [ρ.naturality, affinePointsTarget_natural]

/-- Pull back a regular one-cochain along an actual homomorphism. -/
def OneCochain.precomp (c : OneCochain M G) (f : H ⟶ G) : OneCochain M H where
  value A h := c.value A (H.affinePointsTarget f A h)
  naturality a h := by
    rw [c.naturality, affinePointsTarget_natural]

/-- Pull back a regular two-cochain along an actual homomorphism. -/
def TwoCochain.precomp (c : TwoCochain M G) (f : H ⟶ G) : TwoCochain M H where
  value A h k := c.value A (H.affinePointsTarget f A h) (H.affinePointsTarget f A k)
  naturality a h k := by
    rw [c.naturality, affinePointsTarget_natural, affinePointsTarget_natural]

theorem OneCochain.IsCocycle.precomp {c : OneCochain M G}
    {ρ : ModuleRepresentation M G} (hc : c.IsCocycle ρ) (f : H ⟶ G) :
    (c.precomp f).IsCocycle (ρ.precomp f) := by
  intro A h k
  change c.value A (H.affinePointsTarget f A (h * k)) =
    c.value A (H.affinePointsTarget f A h) +
      ρ.action A (H.affinePointsTarget f A h) (c.value A (H.affinePointsTarget f A k))
  rw [map_mul]
  exact hc A _ _

theorem TwoCochain.IsCocycle.precomp {c : TwoCochain M G}
    {ρ : ModuleRepresentation M G} (hc : c.IsCocycle ρ) (f : H ⟶ G) :
    (c.precomp f).IsCocycle (ρ.precomp f) := by
  intro A h k l
  change c.value A (H.affinePointsTarget f A h) (H.affinePointsTarget f A k) +
      c.value A (H.affinePointsTarget f A (h * k)) (H.affinePointsTarget f A l) =
    ρ.action A (H.affinePointsTarget f A h)
        (c.value A (H.affinePointsTarget f A k) (H.affinePointsTarget f A l)) +
      c.value A (H.affinePointsTarget f A h) (H.affinePointsTarget f A (k * l))
  rw [map_mul, map_mul]
  exact hc A _ _ _

theorem affinePointsTarget_iso_hom_inv (e : H ≅ G) (A : CommAlgCat.{u} R)
    (h : H.affinePoints A) :
    G.affinePointsTarget e.inv A (H.affinePointsTarget e.hom A h) = h := by
  change (h ≫ e.hom.hom.hom) ≫ e.inv.hom.hom = h
  rw [Category.assoc, ← Grp.comp_hom_hom, e.hom_inv_id, Grp.id_hom_hom,
    Category.comp_id]

/-- Low-degree regular cohomology vanishing is invariant under an actual
isomorphism of source group schemes. -/
theorem HasVanishingLowDegreeCohomology.of_iso (e : H ≅ G)
    (hG : HasVanishingLowDegreeCohomology G) : HasVanishingLowDegreeCohomology H := by
  intro M _ _ ρ
  obtain ⟨h₁, h₂⟩ := hG M (ρ.precomp e.inv)
  constructor
  · intro c hc
    obtain ⟨m, hm⟩ := h₁ (c.precomp e.inv) (hc.precomp e.inv)
    refine ⟨m, fun A h => ?_⟩
    have hh := hm A (H.affinePointsTarget e.hom A h)
    change c.value A (G.affinePointsTarget e.inv A (H.affinePointsTarget e.hom A h)) =
      ρ.action A (G.affinePointsTarget e.inv A (H.affinePointsTarget e.hom A h)) _ - _ at hh
    rwa [affinePointsTarget_iso_hom_inv] at hh
  · intro c hc
    obtain ⟨b, hb⟩ := h₂ (c.precomp e.inv) (hc.precomp e.inv)
    refine ⟨b.precomp e.hom, fun A h k => ?_⟩
    have hh := hb A (H.affinePointsTarget e.hom A h) (H.affinePointsTarget e.hom A k)
    change c.value A
        (G.affinePointsTarget e.inv A (H.affinePointsTarget e.hom A h))
        (G.affinePointsTarget e.inv A (H.affinePointsTarget e.hom A k)) +
      b.value A (H.affinePointsTarget e.hom A h * H.affinePointsTarget e.hom A k) =
      ρ.action A
        (G.affinePointsTarget e.inv A (H.affinePointsTarget e.hom A h))
        (b.value A (H.affinePointsTarget e.hom A k)) +
      b.value A (H.affinePointsTarget e.hom A h) at hh
    rw [affinePointsTarget_iso_hom_inv, affinePointsTarget_iso_hom_inv,
      ← map_mul] at hh
    exact hh

/-- Every source diagonalizable in the Library's relative sense has the
required low-degree vanishing over an affine base. -/
theorem hasVanishingLowDegreeCohomology_of_isDiagonalizable
    (hH : RelativeMultiplicativeType.IsDiagonalizable H) :
    HasVanishingLowDegreeCohomology H := by
  obtain ⟨Λ, _, _, ⟨e⟩⟩ := hH
  exact HasVanishingLowDegreeCohomology.of_iso
    (e ≪≫ (Diagonalizable.relativeModelIso R Λ).symm)
    (DiagonalizableModuleAveraging.hasVanishingLowDegreeCohomology Λ)

end Langlands.GroupScheme.Cohomology
