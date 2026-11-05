import Langlands.GroupScheme.AdditiveExtensionCoordinate
import Langlands.GroupScheme.CentralIsogeny.CommutatorDescent
import Langlands.GroupScheme.ActionDescent

/-! # Normalized additive coordinates and descended extension defects -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AdditiveExtensionCoordinate

section Coordinate

variable {B : Scheme.{u}} {E H V : GroupScheme B} (q : E ⟶ H)
    (a : kernel q ⟶ V)

/-- A regular coordinate with prescribed differences on every quotient fibre. -/
def IsFiberCoordinate (f : E.X ⟶ V.X) : Prop :=
  ∀ (T : Over B) (g h : T ⟶ E.X)
    (hgh : g ≫ q.hom.hom = h ≫ q.hom.hom),
    kernelDifference q g h hgh ≫ a.hom.hom = (g ≫ f) * (h ≫ f)⁻¹

/-- Subtract the value at the identity from a regular coordinate. -/
def normalize (f : E.X ⟶ V.X) : E.X ⟶ V.X :=
  f * ((1 : E.X ⟶ E.X) ≫ f)⁻¹

theorem comp_normalize (f : E.X ⟶ V.X) {T : Over B} (g : T ⟶ E.X) :
    g ≫ normalize f = (g ≫ f) * ((1 : T ⟶ E.X) ≫ f)⁻¹ := by
  rw [normalize, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, MonObj.comp_one]

theorem one_normalize (f : E.X ⟶ V.X) (T : Over B) :
    (1 : T ⟶ E.X) ≫ normalize f = 1 := by
  rw [comp_normalize, mul_inv_cancel]

theorem IsFiberCoordinate.normalize {f : E.X ⟶ V.X} (hf : IsFiberCoordinate q a f) :
    IsFiberCoordinate q a (normalize f) := by
  intro T g h hgh
  rw [comp_normalize, comp_normalize, hf T g h hgh]
  group

theorem kernelPoint_quotient {T : Over B} (x : T ⟶ (kernel q).X) :
    (x ≫ (kernelι q).hom.hom) ≫ q.hom.hom = 1 :=
  (kernelPointsEquiv q T x).property

theorem IsFiberCoordinate.mul_left {f : E.X ⟶ V.X} (hf : IsFiberCoordinate q a f)
    {T : Over B} (x : T ⟶ (kernel q).X) (g : T ⟶ E.X) :
    ((x ≫ (kernelι q).hom.hom) * g) ≫ f = (x ≫ a.hom.hom) * (g ≫ f) := by
  have hq : ((x ≫ (kernelι q).hom.hom) * g) ≫ q.hom.hom = g ≫ q.hom.hom := by
    rw [MonObj.mul_comp, kernelPoint_quotient, one_mul]
  have hx : kernelDifference q ((x ≫ (kernelι q).hom.hom) * g) g hq = x := by
    apply (cancel_mono (kernelι q).hom.hom).mp
    rw [kernelDifference_comp, mul_inv_cancel_right]
  have h := hf T _ _ hq
  rw [hx] at h
  exact (eq_mul_inv_iff_mul_eq.mp h).symm

end Coordinate

section Existence

variable {R : CommRingCat.{u}} {E H : GroupScheme (Spec R)} (q : E ⟶ H)
    {n : ℕ} (a : kernel q ⟶ VectorGroup.groupScheme R n)
    [IsAffine E.X.left] [IsAffine H.X.left]
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]

/-- There is a normalized regular coordinate for every homomorphism from the full
kernel to a vector group. -/
theorem exists_normalizedFiberCoordinate :
    ∃ f : E.X ⟶ (VectorGroup.groupScheme R n).X,
      IsFiberCoordinate q a f ∧ ∀ T : Over (Spec R), (1 : T ⟶ E.X) ≫ f = 1 := by
  obtain ⟨f, hf⟩ := exists_fiberCoordinate q a
  exact ⟨normalize f, IsFiberCoordinate.normalize q a hf, one_normalize f⟩

end Existence

section Defect

variable {B : Scheme.{u}} {E H V : GroupScheme B}
    (q : E ⟶ H) (a : kernel q ⟶ V)
    (b : AutomorphicAction H (kernel q)) (c : AutomorphicAction H V)
    (hb : ∀ (T : Over B) (g : T ⟶ E.X) (x : T ⟶ (kernel q).X),
      b.act (g ≫ q.hom.hom) x ≫ (kernelι q).hom.hom =
        g * (x ≫ (kernelι q).hom.hom) * g⁻¹)
    (hc : ∀ (T : Over B) (h : T ⟶ H.X) (x : T ⟶ (kernel q).X),
      b.act h x ≫ a.hom.hom = c.act h (x ≫ a.hom.hom))

include hb hc in
theorem IsFiberCoordinate.mul_right {f : E.X ⟶ V.X} (hf : IsFiberCoordinate q a f)
    {T : Over B} (g : T ⟶ E.X) (x : T ⟶ (kernel q).X) :
    (g * (x ≫ (kernelι q).hom.hom)) ≫ f =
      c.act (g ≫ q.hom.hom) (x ≫ a.hom.hom) * (g ≫ f) := by
  have he : g * (x ≫ (kernelι q).hom.hom) =
      (b.act (g ≫ q.hom.hom) x ≫ (kernelι q).hom.hom) * g := by
    rw [hb]
    group
  rw [he, hf.mul_left q a, hc]

/-- The multiplicativity defect of a regular coordinate on the extension. -/
def defect (f : E.X ⟶ V.X) : E.X ⊗ E.X ⟶ V.X :=
  ((fst E.X E.X * snd E.X E.X) ≫ f) *
    ((fst E.X E.X ≫ f) * c.act (fst E.X E.X ≫ q.hom.hom) (snd E.X E.X ≫ f))⁻¹

theorem lift_defect (f : E.X ⟶ V.X) {T : Over B} (g h : T ⟶ E.X) :
    lift g h ≫ defect q c f =
      ((g * h) ≫ f) * ((g ≫ f) * c.act (g ≫ q.hom.hom) (h ≫ f))⁻¹ := by
  simp only [defect, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc,
    lift_fst, lift_snd, c.naturality]

include hb in
theorem kernelDifference_mul {T : Over B} (g g' h h' : T ⟶ E.X)
    (hg : g ≫ q.hom.hom = g' ≫ q.hom.hom)
    (hh : h ≫ q.hom.hom = h' ≫ q.hom.hom) :
    kernelDifference q (g * h) (g' * h')
        (by rw [MonObj.mul_comp, MonObj.mul_comp, hg, hh]) =
      kernelDifference q g g' hg *
        b.act (g' ≫ q.hom.hom) (kernelDifference q h h' hh) := by
  apply (cancel_mono (kernelι q).hom.hom).mp
  rw [kernelDifference_comp, MonObj.mul_comp, kernelDifference_comp,
    hb, kernelDifference_comp]
  group

private theorem defect_algebra {M : Type*} [CommGroup M] (x x' y y' z z' : M)
    (h : x * x'⁻¹ = (y * y'⁻¹) * (z * z'⁻¹)) :
    x * (y * z)⁻¹ = x' * (y' * z')⁻¹ := by
  apply (mul_inv_eq_mul_inv_iff_mul_eq_mul).mpr
  rw [mul_inv_eq_iff_eq_mul] at h
  rw [h]
  simp [mul_assoc, mul_left_comm, mul_comm]

variable [IsCommMonObj V.X]

include hb hc in
/-- The regular defect depends only on the two quotient points. -/
theorem IsFiberCoordinate.defect_eq {f : E.X ⟶ V.X} (hf : IsFiberCoordinate q a f)
    {T : Over B} (g g' h h' : T ⟶ E.X)
    (hg : g ≫ q.hom.hom = g' ≫ q.hom.hom)
    (hh : h ≫ q.hom.hom = h' ≫ q.hom.hom) :
    lift g h ≫ defect q c f = lift g' h' ≫ defect q c f := by
  have hp := hf T (g * h) (g' * h')
    (by rw [MonObj.mul_comp, MonObj.mul_comp, hg, hh])
  rw [kernelDifference_mul q b hb g g' h h' hg hh, MonObj.mul_comp,
    hc, hf T g g' hg, hf T h h' hh, c.act_mul_right, c.act_inv] at hp
  rw [lift_defect, lift_defect, hg]
  exact defect_algebra _ _ _ _ _ _ hp.symm

include hb hc in
/-- The defect coequalizes the relation of the quotient square. -/
theorem IsFiberCoordinate.defect_comp_eq {f : E.X ⟶ V.X} (hf : IsFiberCoordinate q a f)
    {T : Over B} (x y : T ⟶ E.X ⊗ E.X)
    (hxy : x ≫ (q.hom.hom ⊗ₘ q.hom.hom) = y ≫ (q.hom.hom ⊗ₘ q.hom.hom)) :
    x ≫ defect q c f = y ≫ defect q c f := by
  have h₁ : (x ≫ fst E.X E.X) ≫ q.hom.hom = (y ≫ fst E.X E.X) ≫ q.hom.hom := by
    simpa only [Category.assoc, tensorHom_fst] using congrArg (· ≫ fst H.X H.X) hxy
  have h₂ : (x ≫ snd E.X E.X) ≫ q.hom.hom = (y ≫ snd E.X E.X) ≫ q.hom.hom := by
    simpa only [Category.assoc, tensorHom_snd] using congrArg (· ≫ snd H.X H.X) hxy
  simpa only [lift_comp_fst_snd] using
    hf.defect_eq q a b c hb hc
      (x ≫ fst E.X E.X) (y ≫ fst E.X E.X)
      (x ≫ snd E.X E.X) (y ≫ snd E.X E.X) h₁ h₂

include hb hc in
/-- The same quotient relation for maps of underlying schemes. -/
theorem IsFiberCoordinate.scheme_defect_comp_eq {f : E.X ⟶ V.X}
    (hf : IsFiberCoordinate q a f) {Z : Scheme.{u}}
    (x y : Z ⟶ (E.X ⊗ E.X).left)
    (hxy : x ≫ (q.hom.hom ⊗ₘ q.hom.hom).left =
      y ≫ (q.hom.hom ⊗ₘ q.hom.hom).left) :
    x ≫ (defect q c f).left = y ≫ (defect q c f).left := by
  have hs : y ≫ (E.X ⊗ E.X).hom = x ≫ (E.X ⊗ E.X).hom := by
    rw [← Over.w (q.hom.hom ⊗ₘ q.hom.hom), ← Category.assoc, ← hxy, Category.assoc]
  let x₀ : Over.mk (x ≫ (E.X ⊗ E.X).hom) ⟶ E.X ⊗ E.X := Over.homMk x rfl
  let y₀ : Over.mk (x ≫ (E.X ⊗ E.X).hom) ⟶ E.X ⊗ E.X := Over.homMk y hs
  exact congrArg (fun z => z.left)
    (hf.defect_comp_eq q a b c hb hc x₀ y₀ (Over.OverMorphism.ext hxy))

/-- Every regular coordinate has the twisted two-cocycle identity on lifts. -/
theorem defect_cocycle (f : E.X ⟶ V.X) {T : Over B} (g h l : T ⟶ E.X) :
    (lift g h ≫ defect q c f) * (lift (g * h) l ≫ defect q c f) =
      (lift g (h * l) ≫ defect q c f) *
        c.act (g ≫ q.hom.hom) (lift h l ≫ defect q c f) := by
  simp only [lift_defect, MonObj.mul_comp, c.act_mul_right, c.act_inv,
    c.act_mul_left, mul_assoc]
  simp [mul_inv_rev, mul_assoc, mul_left_comm, mul_comm]

variable [QuasiCompact q.hom.hom.left] [Flat q.hom.hom.left]
    [Surjective q.hom.hom.left]
    (f : E.X ⟶ V.X) (hf : IsFiberCoordinate q a f)

/-- The descended defect as an underlying scheme morphism. -/
def quotientDefectSchemeHom : (H.X ⊗ H.X).left ⟶ V.X.left :=
  haveI := CommutatorDescent.effectiveEpi_tensorHom q
  EffectiveEpi.desc (q.hom.hom ⊗ₘ q.hom.hom).left (defect q c f).left
    (fun x y hxy => hf.scheme_defect_comp_eq q a b c hb hc x y hxy)

@[reassoc]
theorem fac_quotientDefectSchemeHom :
    (q.hom.hom ⊗ₘ q.hom.hom).left ≫ quotientDefectSchemeHom q a b c hb hc f hf =
      (defect q c f).left :=
  haveI := CommutatorDescent.effectiveEpi_tensorHom q
  EffectiveEpi.fac _ _ _

/-- The multiplicativity defect descended to the quotient square over the base. -/
def quotientDefect : H.X ⊗ H.X ⟶ V.X :=
  Over.homMk (quotientDefectSchemeHom q a b c hb hc f hf) (by
    have := CommutatorDescent.effectiveEpi_tensorHom q
    apply (cancel_epi (q.hom.hom ⊗ₘ q.hom.hom).left).mp
    rw [fac_quotientDefectSchemeHom_assoc, Over.w, Over.w])

@[reassoc]
theorem fac_quotientDefect :
    (q.hom.hom ⊗ₘ q.hom.hom) ≫ quotientDefect q a b c hb hc f hf = defect q c f :=
  Over.OverMorphism.ext (fac_quotientDefectSchemeHom q a b c hb hc f hf)

/-- On points admitting lifts, the descended defect is the original defect. -/
theorem lift_quotientDefect_eq {T : Over B} (g h : T ⟶ E.X) :
    lift (g ≫ q.hom.hom) (h ≫ q.hom.hom) ≫ quotientDefect q a b c hb hc f hf =
      lift g h ≫ defect q c f := by
  rw [← lift_map, Category.assoc, fac_quotientDefect]

/-- Evaluation on lifted points is the multiplicativity defect of the coordinate. -/
theorem lift_quotientDefect {T : Over B} (g h : T ⟶ E.X) :
    lift (g ≫ q.hom.hom) (h ≫ q.hom.hom) ≫ quotientDefect q a b c hb hc f hf =
      ((g * h) ≫ f) * ((g ≫ f) * c.act (g ≫ q.hom.hom) (h ≫ f))⁻¹ := by
  rw [← lift_map, Category.assoc, fac_quotientDefect, lift_defect]

/-- Evaluation of the descended regular defect is natural on all test schemes. -/
theorem quotientDefect_naturality {T T' : Over B} (v : T' ⟶ T)
    (g h : T ⟶ H.X) :
    v ≫ (lift g h ≫ quotientDefect q a b c hb hc f hf) =
      lift (v ≫ g) (v ≫ h) ≫ quotientDefect q a b c hb hc f hf := by
  rw [← Category.assoc, comp_lift]

/-- The descended defect satisfies the twisted two-cocycle law on every test scheme. -/
theorem quotientDefect_cocycle {T : Over B} (g h l : T ⟶ H.X) :
    (lift g h ≫ quotientDefect q a b c hb hc f hf) *
        (lift (g * h) l ≫ quotientDefect q a b c hb hc f hf) =
      (lift g (h * l) ≫ quotientDefect q a b c hb hc f hf) *
        c.act g (lift h l ≫ quotientDefect q a b c hb hc f hf) := by
  apply AutomorphicAction.hom_ext_of_local_quotient_lift q g
  intro T₁ v g' hg
  simp only [MonObj.comp_mul, quotientDefect_naturality, c.naturality, hg]
  apply AutomorphicAction.hom_ext_of_local_quotient_lift q (v ≫ h)
  intro T₂ w h' hh
  simp only [MonObj.comp_mul, quotientDefect_naturality, c.naturality, hh]
  apply AutomorphicAction.hom_ext_of_local_quotient_lift q (w ≫ (v ≫ l))
  intro T₃ z l' hl
  simp only [MonObj.comp_mul, quotientDefect_naturality, c.naturality, hl]
  simp only [← Category.assoc, ← MonObj.mul_comp, lift_quotientDefect_eq]
  simpa only [← Category.assoc] using defect_cocycle q c f (z ≫ w ≫ g') (z ≫ h') l'

end Defect

end Langlands.GroupScheme.AdditiveExtensionCoordinate
