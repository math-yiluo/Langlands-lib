import Langlands.Geometry.FormalGroup.LocalQuasiIsogenyCoefficientCoherence
import Langlands.Geometry.FormalGroup.LocalQuasiIsogenyComposition
import Langlands.Geometry.FormalGroup.FiniteKernelComposition
import Langlands.Geometry.FormalGroup.LocalQuasiIsogenyInverseProof
import Langlands.Geometry.FormalGroup.RationalSectionIsoTransport
import Langlands.Geometry.FormalGroup.RationalSectionBaseChangeCalculus

/-! # The groupoid laws of actual local quasi-isogenies -/

noncomputable section
universe u v

namespace Langlands.FormalGroup.ModuleLaw.LocalQuasiIsogeny
open CategoryTheory Opposite TopologicalSpace

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R S : Type v} [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
variable {F : Type v} [Field F] [Algebra O F]
variable {σ τ υ ω σ' τ' υ' : Type} [Finite σ] [Finite τ] [Finite υ] [Finite ω]
variable [Finite σ'] [Finite τ'] [Finite υ']
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {P : ModuleLaw O R υ} {Q : ModuleLaw O R ω}
variable {M' : ModuleLaw O R σ'} {N' : ModuleLaw O R τ'} {P' : ModuleLaw O R υ'}
variable {π : O} {U V : Opens (PrimeSpectrum R)}

/-- Compose actual local quasi-isogenies using the finite projective kernel theorem. -/
def comp (g : LocalQuasiIsogeny F π N P U) (f : LocalQuasiIsogeny F π M N U) :
    LocalQuasiIsogeny F π M P U :=
  comp_of_finiteKernelComposition (M := M) (N := N) (P := P)
    (fun _ => Hom.finiteKernelCompositionStatement _ _ _) g f

@[simp]
theorem comp_val (g : LocalQuasiIsogeny F π N P U) (f : LocalQuasiIsogeny F π M N U) :
    (g.comp f).val = RationalSection.comp g.val f.val := rfl

/-- Lift a local quasi-isogeny to its unique pair of inverse rational sections. -/
def toSectionIso (f : LocalQuasiIsogeny F π M N U) : RationalSectionIso F M N U :=
  ((localQuasiIsogenyInverse F π M N U f).exists).choose

@[simp]
theorem toSectionIso_hom (f : LocalQuasiIsogeny F π M N U) : f.toSectionIso.hom = f.val :=
  ((localQuasiIsogenyInverse F π M N U f).exists).choose_spec.1

theorem toSectionIso_inv_isLocal (f : LocalQuasiIsogeny F π M N U) :
    RationalSection.IsLocallyScalarIsogeny π f.toSectionIso.inv :=
  ((localQuasiIsogenyInverse F π M N U f).exists).choose_spec.2

/-- The actual reverse rational section is itself a local quasi-isogeny. -/
def inv (f : LocalQuasiIsogeny F π M N U) : LocalQuasiIsogeny F π N M U where
  scalar_ne_zero := f.scalar_ne_zero
  source_divisible := f.target_divisible
  target_divisible := f.source_divisible
  val := f.toSectionIso.inv
  isLocal := f.toSectionIso_inv_isLocal

@[simp]
theorem inv_val (f : LocalQuasiIsogeny F π M N U) : f.inv.val = f.toSectionIso.inv := rfl

@[simp]
theorem toSectionIso_idOn (hπ : algebraMap O F π ≠ 0) (hM : M.IsPiDivisible π) :
    (idOn π hπ M hM U).toSectionIso = RationalSectionIso.refl M U := by
  apply RationalSectionIso.ext
  exact toSectionIso_hom _

@[simp]
theorem toSectionIso_comp (g : LocalQuasiIsogeny F π N P U) (f : LocalQuasiIsogeny F π M N U) :
    (g.comp f).toSectionIso = f.toSectionIso.trans g.toSectionIso := by
  apply RationalSectionIso.ext
  change (g.comp f).toSectionIso.hom = RationalSection.comp g.toSectionIso.hom f.toSectionIso.hom
  simp only [toSectionIso_hom, comp_val]

@[simp]
theorem toSectionIso_inv (f : LocalQuasiIsogeny F π M N U) :
    f.inv.toSectionIso = f.toSectionIso.symm := by
  apply RationalSectionIso.ext
  exact toSectionIso_hom _

@[simp]
theorem idOn_comp (f : LocalQuasiIsogeny F π M N U) :
    (idOn π f.scalar_ne_zero N f.target_divisible U).comp f = f := by
  apply ext
  exact RationalSection.id_comp f.val

@[simp]
theorem comp_idOn (f : LocalQuasiIsogeny F π M N U) :
    f.comp (idOn π f.scalar_ne_zero M f.source_divisible U) = f := by
  apply ext
  exact RationalSection.comp_id f.val

theorem comp_assoc (h : LocalQuasiIsogeny F π P Q U) (g : LocalQuasiIsogeny F π N P U)
    (f : LocalQuasiIsogeny F π M N U) : (h.comp g).comp f = h.comp (g.comp f) := by
  apply ext
  exact RationalSection.comp_assoc h.val g.val f.val

@[simp]
theorem inv_comp_self (f : LocalQuasiIsogeny F π M N U) :
    f.inv.comp f = idOn π f.scalar_ne_zero M f.source_divisible U := by
  apply ext
  change RationalSection.comp f.toSectionIso.inv f.val = RationalSection.id M U
  simpa only [toSectionIso_hom] using f.toSectionIso.inv_hom

@[simp]
theorem self_comp_inv (f : LocalQuasiIsogeny F π M N U) :
    f.comp f.inv = idOn π f.scalar_ne_zero N f.target_divisible U := by
  apply ext
  change RationalSection.comp f.val f.toSectionIso.inv = RationalSection.id N U
  simpa only [toSectionIso_hom] using f.toSectionIso.hom_inv

@[simp]
theorem inv_inv (f : LocalQuasiIsogeny F π M N U) : f.inv.inv = f := by
  apply ext
  change f.inv.toSectionIso.inv = f.val
  rw [toSectionIso_inv]
  exact f.toSectionIso_hom

@[simp]
theorem inv_comp (g : LocalQuasiIsogeny F π N P U) (f : LocalQuasiIsogeny F π M N U) :
    (g.comp f).inv = f.inv.comp g.inv := by
  apply ext
  simp only [comp_val, inv_val, toSectionIso_comp]
  rfl

@[simp]
theorem restrict_comp_hom (g : LocalQuasiIsogeny F π N P U) (f : LocalQuasiIsogeny F π M N U)
    (i : V ⟶ U) : (g.comp f).restrict i = (g.restrict i).comp (f.restrict i) := by
  apply ext
  exact RationalSection.restrict_comp_hom i g.val f.val

@[simp]
theorem toSectionIso_restrict (f : LocalQuasiIsogeny F π M N U) (i : V ⟶ U) :
    (f.restrict i).toSectionIso = f.toSectionIso.restrict i := by
  apply RationalSectionIso.ext
  change (f.restrict i).toSectionIso.hom = RationalSection.restrict i f.toSectionIso.hom
  rw [toSectionIso_hom, toSectionIso_hom]
  rfl

@[simp]
theorem restrict_inv (f : LocalQuasiIsogeny F π M N U) (i : V ⟶ U) :
    f.inv.restrict i = (f.restrict i).inv := by
  apply ext
  change RationalSection.restrict i f.toSectionIso.inv = (f.restrict i).toSectionIso.inv
  rw [toSectionIso_restrict]
  rfl

theorem baseChange_comp (g : LocalQuasiIsogeny F π N P U) (f : LocalQuasiIsogeny F π M N U)
    (φ : R →ₐ[O] S) : (g.comp f).baseChange φ = (g.baseChange φ).comp (f.baseChange φ) := by
  apply ext
  exact RationalSection.baseChange_comp φ g.val f.val

@[simp]
theorem toSectionIso_baseChange (f : LocalQuasiIsogeny F π M N U) (φ : R →ₐ[O] S) :
    (f.baseChange φ).toSectionIso = f.toSectionIso.baseChange φ := by
  apply RationalSectionIso.ext
  change (f.baseChange φ).toSectionIso.hom = RationalSection.baseChange φ U f.toSectionIso.hom
  rw [toSectionIso_hom, toSectionIso_hom]
  rfl

@[simp]
theorem baseChange_inv (f : LocalQuasiIsogeny F π M N U) (φ : R →ₐ[O] S) :
    f.inv.baseChange φ = (f.baseChange φ).inv := by
  apply ext
  change RationalSection.baseChange φ U f.toSectionIso.inv = (f.baseChange φ).toSectionIso.inv
  rw [toSectionIso_baseChange]
  rfl

@[simp]
theorem transportIso_idOn (a : Iso M M') (hπ : algebraMap O F π ≠ 0) (hM : M.IsPiDivisible π) :
    (idOn π hπ M hM U).transportIso a a = idOn π hπ M' (a.isPiDivisible π hM) U := by
  apply ext
  exact RationalSection.transportIso_id a U

theorem transportIso_comp (g : LocalQuasiIsogeny F π N P U) (f : LocalQuasiIsogeny F π M N U)
    (a : Iso M M') (b : Iso N N') (c : Iso P P') :
    (g.comp f).transportIso a c = (g.transportIso b c).comp (f.transportIso a b) := by
  apply ext
  exact RationalSection.transportIso_comp a b c g.val f.val

@[simp]
theorem toSectionIso_transportIso (f : LocalQuasiIsogeny F π M N U) (a : Iso M M') (b : Iso N N') :
    (f.transportIso a b).toSectionIso = f.toSectionIso.transportIso a b := by
  apply RationalSectionIso.ext
  change (f.transportIso a b).toSectionIso.hom = RationalSection.transportIso a b U f.toSectionIso.hom
  rw [toSectionIso_hom, toSectionIso_hom]
  rfl

@[simp]
theorem transportIso_inv (f : LocalQuasiIsogeny F π M N U) (a : Iso M M') (b : Iso N N') :
    f.inv.transportIso b a = (f.transportIso a b).inv := by
  apply ext
  change RationalSection.transportIso b a U f.toSectionIso.inv = (f.transportIso a b).toSectionIso.inv
  rw [toSectionIso_transportIso]
  rfl

end Langlands.FormalGroup.ModuleLaw.LocalQuasiIsogeny
