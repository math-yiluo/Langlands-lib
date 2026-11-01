import Langlands.Representation.Induction.Definitions
import Mathlib.Basic.Complex.Basic

/-! Elementary invariant-character extension along a split group retraction. -/

namespace Langlands.Induction.SplitKernelLocalization

universe uG uL

variable {G : Type uG} [Group G] {L : Type uL} [Group L]
variable (r : G →* L) (s : L →* G)

/-- Inverse conjugation by an actual section value, in the actual kernel. -/
def kernelConjugate (l : L) (n : r.ker) : r.ker :=
  ⟨(s l)⁻¹ * (n : G) * s l, by
    change r ((s l)⁻¹ * (n : G) * s l) = 1
    simp only [map_mul, map_inv, show r (n : G) = 1 from n.property,
      mul_one, inv_mul_cancel]⟩

@[simp] theorem kernelConjugate_val (l : L) (n : r.ker) :
    (kernelConjugate r s l n : G) = (s l)⁻¹ * (n : G) * s l := rfl

/-- The given kernel character is fixed by inverse section conjugation. -/
def SectionInvariant (theta : r.ker →* ℂˣ) : Prop :=
  ∀ (l : L) (n : r.ker), theta (kernelConjugate r s l n) = theta n

variable (hrs : ∀ l, r (s l) = l)

/-- The actual kernel coordinate in the decomposition `g = n * s (r g)`. -/
def kernelCoordinate (g : G) : r.ker :=
  ⟨g * (s (r g))⁻¹, by
    change r (g * (s (r g))⁻¹) = 1
    simp only [map_mul, map_inv, hrs, mul_inv_cancel]⟩

@[simp] theorem kernelCoordinate_val (g : G) :
    (kernelCoordinate r s hrs g : G) = g * (s (r g))⁻¹ := rfl

theorem kernelCoordinate_mul (g h : G) :
    kernelCoordinate r s hrs (g * h) =
      kernelCoordinate r s hrs g *
        kernelConjugate r s (r g)⁻¹ (kernelCoordinate r s hrs h) := by
  apply Subtype.ext
  simp [kernelCoordinate, kernelConjugate, map_mul, mul_inv_rev, mul_assoc]

@[simp] theorem kernelCoordinate_one :
    kernelCoordinate r s hrs 1 = 1 := by
  apply Subtype.ext
  simp [kernelCoordinate]

@[simp] theorem kernelCoordinate_kernel (n : r.ker) :
    kernelCoordinate r s hrs (n : G) = n := by
  apply Subtype.ext
  simp [kernelCoordinate, show r (n : G) = 1 from n.property]

@[simp] theorem kernelCoordinate_section (l : L) :
    kernelCoordinate r s hrs (s l) = 1 := by
  apply Subtype.ext
  simp [kernelCoordinate, hrs]

variable (theta : r.ker →* ℂˣ) (hTheta : SectionInvariant r s theta)

/-- Extend an invariant kernel character, trivializing it on the section. -/
def characterExtension : G →* ℂˣ where
  toFun g := theta (kernelCoordinate r s hrs g)
  map_one' := by rw [kernelCoordinate_one, map_one]
  map_mul' g h := by
    rw [kernelCoordinate_mul, map_mul, hTheta]

@[simp] theorem characterExtension_apply (g : G) :
    characterExtension r s hrs theta hTheta g =
      theta (kernelCoordinate r s hrs g) := rfl

@[simp] theorem characterExtension_kernel (n : r.ker) :
    characterExtension r s hrs theta hTheta (n : G) = theta n := by
  simp

@[simp] theorem characterExtension_section (l : L) :
    characterExtension r s hrs theta hTheta (s l) = 1 := by
  simp

theorem characterExtension_mul (g h : G) :
    characterExtension r s hrs theta hTheta (g * h) =
      characterExtension r s hrs theta hTheta g *
        characterExtension r s hrs theta hTheta h :=
  map_mul _ g h

/-- The extension kernel is exactly the preimage of the given open kernel. -/
theorem characterExtension_ker :
    ((characterExtension r s hrs theta hTheta).ker : Set G) =
      (kernelCoordinate r s hrs) ⁻¹' (theta.ker : Set r.ker) := by
  ext g
  rfl

section Topology

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace L]

/-- The split kernel coordinate is continuous in the induced kernel topology. -/
theorem continuous_kernelCoordinate (hr : Continuous r) (hs : Continuous s) :
    Continuous (kernelCoordinate r s hrs) :=
  (continuous_id.mul (hs.comp hr).inv).subtype_mk _

/-- Extending an actual open-kernel character gives an actual smooth character. -/
def smoothCharacterExtension (hr : Continuous r) (hs : Continuous s)
    (theta : SmoothCharacter ℂ r.ker)
    (hTheta : SectionInvariant r s theta.toMonoidHom) : SmoothCharacter ℂ G where
  toMonoidHom := characterExtension r s hrs theta.toMonoidHom hTheta
  isOpen_ker := by
    change IsOpen ((kernelCoordinate r s hrs) ⁻¹'
      (theta.toMonoidHom.ker : Set r.ker))
    exact theta.isOpen_ker.preimage (continuous_kernelCoordinate r s hrs hr hs)

@[simp] theorem smoothCharacterExtension_toMonoidHom
    (hr : Continuous r) (hs : Continuous s)
    (theta : SmoothCharacter ℂ r.ker) (hTheta : SectionInvariant r s theta.toMonoidHom) :
    (smoothCharacterExtension r s hrs hr hs theta hTheta).toMonoidHom =
      characterExtension r s hrs theta.toMonoidHom hTheta := rfl

end Topology

end Langlands.Induction.SplitKernelLocalization
