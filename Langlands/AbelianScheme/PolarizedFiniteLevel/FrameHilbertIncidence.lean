import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameHilbertLocusStatement
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Incidence of marked sections in a projective closed family -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry

namespace FrameHilbert

variable {S T : Scheme.{u}} {m : ℕ}

/-- The structure morphism of the projective closed family cut out by `I`. -/
abbrev projection (I : (RelativeProjectiveSpace S m).IdealSheafData) : I.subscheme ⟶ S :=
  I.subschemeι ≫ RelativeProjectiveSpace.toBase S m

/-- The morphism from the closed family after a change of base to the original family. -/
def subschemeBaseChange (I : (RelativeProjectiveSpace S m).IdealSheafData) (t : T ⟶ S) :
    (I.comap (RelativeProjectiveSpace.map m t)).subscheme ⟶ I.subscheme :=
  Scheme.IdealSheafData.subschemeMap _ I _ (I.le_map_comap _)

@[reassoc (attr := simp)]
theorem subschemeBaseChange_subschemeι (I : (RelativeProjectiveSpace S m).IdealSheafData)
    (t : T ⟶ S) :
    subschemeBaseChange I t ≫ I.subschemeι =
      (I.comap (RelativeProjectiveSpace.map m t)).subschemeι ≫ RelativeProjectiveSpace.map m t :=
  Scheme.IdealSheafData.subschemeMap_subschemeι ..

/-- The base-changed ideal cuts out the Cartesian base change of the family over `S`. -/
theorem isPullback_subschemeBaseChange (I : (RelativeProjectiveSpace S m).IdealSheafData)
    (t : T ⟶ S) :
    IsPullback (subschemeBaseChange I t) (projection (I.comap (RelativeProjectiveSpace.map m t)))
      (projection I) t := by
  have hs := isPullback_of_isClosedImmersion
    (I.comap (RelativeProjectiveSpace.map m t)).subschemeι I.subschemeι
    (subschemeBaseChange I t) (RelativeProjectiveSpace.map m t) (by simp) (by simp)
  exact hs.flip.paste_vert (RelativeProjectiveSpace.isPullback_map m t).flip

private theorem factorsThrough_subscheme_iff {X Y : Scheme.{u}}
    (J : Y.IdealSheafData) (f : X ⟶ Y) :
    (∃ g : X ⟶ J.subscheme, g ≫ J.subschemeι = f) ↔ J ≤ f.ker := by
  constructor
  · rintro ⟨g, rfl⟩
    exact J.ker_subschemeι.ge.trans (g.le_ker_comp _)
  · intro h
    rw [← J.ker_subschemeι] at h
    exact ⟨IsClosedImmersion.lift J.subschemeι f h, IsClosedImmersion.lift_fac _ _ _⟩

/-- The sum of the ideals obtained by pulling the family ideal back along all the ambient marks. -/
def incidenceIdeal {R : Type v} (I : (RelativeProjectiveSpace S m).IdealSheafData)
    (σ : R → (S ⟶ ProjectiveSpace (ULift.{u} ℤ) m)) : S.IdealSheafData :=
  ⨆ r, I.comap (RelativeProjectiveSpace.lift m (𝟙 S) (σ r))

/-- The incidence subscheme represents factoring of every ambient mark through the
base-changed family, including on nonreduced test bases. -/
theorem factorsThrough_incidence_iff {R : Type v}
    (I : (RelativeProjectiveSpace S m).IdealSheafData)
    (σ : R → (S ⟶ ProjectiveSpace (ULift.{u} ℤ) m)) (t : T ⟶ S) :
    (∃ t' : T ⟶ (incidenceIdeal I σ).subscheme, t' ≫ (incidenceIdeal I σ).subschemeι = t) ↔
      ∀ r, ∃ q : T ⟶ (I.comap (RelativeProjectiveSpace.map m t)).subscheme,
        q ≫ (I.comap (RelativeProjectiveSpace.map m t)).subschemeι =
          RelativeProjectiveSpace.lift m (𝟙 T) (t ≫ σ r) := by
  simp only [factorsThrough_subscheme_iff, incidenceIdeal, iSup_le_iff]
  refine forall_congr' fun r => ?_
  rw [← Scheme.IdealSheafData.le_map_iff_comap_le, Scheme.IdealSheafData.map_ker]
  have h : t ≫ RelativeProjectiveSpace.lift m (𝟙 S) (σ r) =
      RelativeProjectiveSpace.lift m (𝟙 T) (t ≫ σ r) ≫ RelativeProjectiveSpace.map m t := by
    apply RelativeProjectiveSpace.hom_ext <;> simp
  rw [h, Scheme.Hom.ker_comp, Scheme.IdealSheafData.le_map_iff_comap_le]

end FrameHilbert

variable {P : Prerequisites.{u}} {S : Scheme.{u}} {g d n m : ℕ}
  {a : Datum P S g d n} {ψ : a.abelian.X.left ⟶ RelativeProjectiveSpace S m}
  {I : (RelativeProjectiveSpace S m).IdealSheafData}
  {σ : (Fin (2 * g) → ZMod n) → (S ⟶ ProjectiveSpace (ULift.{u} ℤ) m)}

/-- A closed embedding realizing the family identifies the abelian scheme with the family's
closed subscheme. -/
def Datum.Realizes.subschemeIso (h : a.Realizes ψ I σ) [IsClosedImmersion ψ] :
    a.abelian.X.left ≅ I.subscheme :=
  asIso ψ.toImage ≪≫ eqToIso (congrArg Scheme.IdealSheafData.subscheme h.1)

@[reassoc (attr := simp)]
theorem Datum.Realizes.subschemeIso_hom_subschemeι (h : a.Realizes ψ I σ)
    [IsClosedImmersion ψ] : h.subschemeIso.hom ≫ I.subschemeι = ψ := by
  unfold Datum.Realizes.subschemeIso
  generalize hker : ψ.ker = J at h
  obtain rfl := h.1.symm
  simp

/-- In a realization, every supplied mark is the image of the corresponding torsion point
under the isomorphism with the closed family. -/
theorem Datum.Realizes.torsionPoint_subschemeIso (h : a.Realizes ψ I σ)
    {ρ : Fin (m + 2) → Fin (2 * g) → ZMod n} (he : a.IsFrameEmbedding ρ ψ)
    (r : Fin (2 * g) → ZMod n) :
    letI := he.isClosedImmersion
    a.torsionPoint r ≫ h.subschemeIso.hom ≫ I.subschemeι =
      RelativeProjectiveSpace.lift m (𝟙 S) (σ r) := by
  let := he.isClosedImmersion
  rw [h.subschemeIso_hom_subschemeι]
  apply RelativeProjectiveSpace.hom_ext
  · simp [he.toBase]
  · simpa only [Category.assoc, RelativeProjectiveSpace.lift_toIntegral] using h.2 r

end Langlands.AbelianScheme.PolarizedFiniteLevel
