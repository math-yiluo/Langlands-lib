import Langlands.AlgebraicGeometry.AffineCechDeRham
import Langlands.AlgebraicGeometry.Modules.LineBundleSectionClearingProof
import Langlands.AlgebraicGeometry.Picard.DualScheme

/-!
# The first Chern cocycle of a line bundle in the affine Čech–de Rham complex

Let `f : X ⟶ Spec R` be a scheme over an affine base, `U` an affine open cover of `X` and
`L` an actual line bundle on `X` with a trivialization on every member of `U`.
A trivialization on an open `V` is recorded as a `LocalFrame`: a section `e` of `L` on `V`
such that `a ↦ a • e` is a bijection from functions to sections on every open inside `V`.
`LocalFrame.ofIso` produces the frame `τ⁻¹(1)` of an isomorphism
`τ : L|_V ≅ 𝒪_V`.

The transition unit `g_σ` on `U_{σ 0} ∩ U_{σ 1}` is defined by `e_{σ 1} = g_σ • e_{σ 0}`;
for isomorphisms it is `τ_{σ 0} τ_{σ 1}⁻¹(1)`. With the face convention of `cechD`,
`(∂h)_{01} = h_1 - h_0`, these units satisfy `g_{01} g_{12} = g_{02}`.
`firstChernCocycle` is the element `(0, (g_σ⁻¹ dg_σ)_σ, 0)` of `C2`.
It satisfies the Čech and exterior closure equations, changes by the total boundary
`D1 (0, (u_i⁻¹ du_i)_i)` when the frames change by `e'_i = u_i • e_i`, and restricts
along affine refinements. `poincareFirstChernCocycle` specializes it to the Poincaré line
bundle on `A ×_S A^∨`.

This is the degree-two first Chern class construction underlying the de Rham pairing of
Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*, revised
14 March 2021, the discussion before Corollary 2.2.4.8, printed p. 156 (PDF p. 184),
in the Čech–de Rham conventions of its §2.1.6. The retained source is
`lan-2008-pel-thesis-revision-2021`.
-/

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AffineCechDeRham

open Langlands.AlgebraicGeometry.Picard

section Frames

variable {X : Scheme.{u}} (L : LineBundle X)

/-- A trivialization of `L` on `V`, given by a frame. -/
structure LocalFrame (V : X.Opens) where
  /-- The frame section. -/
  frame : Γ(L.obj, V)
  /-- Multiplying the restricted frame by functions is bijective on every smaller open. -/
  bijective : ∀ (W : X.Opens) (h : W ≤ V),
    Function.Bijective fun a : Γ(X, W) => a • L.obj.presheaf.map (homOfLE h).op frame

namespace LocalFrame

variable {L} {V V₁ V₂ V₃ : X.Opens}

/-- The frame restricted to a smaller open. -/
abbrev restrictFrame (e : LocalFrame L V) {W : X.Opens} (h : W ≤ V) : Γ(L.obj, W) :=
  L.obj.presheaf.map (homOfLE h).op e.frame

lemma restrictFrame_restrict (e : LocalFrame L V) {W W' : X.Opens} (h : W ≤ V) (h' : W' ≤ W) :
    L.obj.presheaf.map (homOfLE h').op (e.restrictFrame h) = e.restrictFrame (h'.trans h) := by
  rw [restrictFrame, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The coordinate of a section in the restricted frame. -/
def coord (e : LocalFrame L V) {W : X.Opens} (h : W ≤ V) (s : Γ(L.obj, W)) : Γ(X, W) :=
  (Equiv.ofBijective _ (e.bijective W h)).symm s

lemma coord_smul (e : LocalFrame L V) {W : X.Opens} (h : W ≤ V) (s : Γ(L.obj, W)) :
    e.coord h s • e.restrictFrame h = s :=
  (Equiv.ofBijective _ (e.bijective W h)).apply_symm_apply s

lemma coord_eq (e : LocalFrame L V) {W : X.Opens} (h : W ≤ V) {s : Γ(L.obj, W)} {a : Γ(X, W)}
    (hs : a • e.restrictFrame h = s) : e.coord h s = a :=
  (Equiv.ofBijective _ (e.bijective W h)).symm_apply_eq.mpr hs.symm

lemma smul_injective (e : LocalFrame L V) {W : X.Opens} (h : W ≤ V) {a b : Γ(X, W)}
    (hab : a • e.restrictFrame h = b • e.restrictFrame h) : a = b :=
  (e.bijective W h).1 hab

/-- The restriction of a frame to a smaller open. -/
def restrict (e : LocalFrame L V) {W : X.Opens} (h : W ≤ V) : LocalFrame L W where
  frame := e.restrictFrame h
  bijective W' h' := by
    simpa only [restrictFrame_restrict] using e.bijective W' (h'.trans h)

@[simp]
lemma restrict_frame (e : LocalFrame L V) {W : X.Opens} (h : W ≤ V) :
    (e.restrict h).frame = e.restrictFrame h := rfl

lemma restrict_restrictFrame (e : LocalFrame L V) {W W' : X.Opens} (h : W ≤ V) (h' : W' ≤ W) :
    (e.restrict h).restrictFrame h' = e.restrictFrame (h'.trans h) :=
  e.restrictFrame_restrict h h'

/-- The transition unit `g` on `W`, characterized by `e₂ = g • e₁` there. -/
def transition (e₁ : LocalFrame L V₁) (e₂ : LocalFrame L V₂) {W : X.Opens}
    (h₁ : W ≤ V₁) (h₂ : W ≤ V₂) : Γ(X, W)ˣ where
  val := e₁.coord h₁ (e₂.restrictFrame h₂)
  inv := e₂.coord h₂ (e₁.restrictFrame h₁)
  val_inv := by
    refine e₂.smul_injective h₂ ?_
    rw [mul_smul, e₂.coord_smul, e₁.coord_smul, one_smul]
  inv_val := by
    refine e₁.smul_injective h₁ ?_
    rw [mul_smul, e₁.coord_smul, e₂.coord_smul, one_smul]

lemma transition_smul (e₁ : LocalFrame L V₁) (e₂ : LocalFrame L V₂) {W : X.Opens}
    (h₁ : W ≤ V₁) (h₂ : W ≤ V₂) :
    (transition e₁ e₂ h₁ h₂ : Γ(X, W)) • e₁.restrictFrame h₁ = e₂.restrictFrame h₂ :=
  e₁.coord_smul h₁ _

lemma transition_val_eq (e₁ : LocalFrame L V₁) (e₂ : LocalFrame L V₂) {W : X.Opens}
    (h₁ : W ≤ V₁) (h₂ : W ≤ V₂) {a : Γ(X, W)}
    (ha : a • e₁.restrictFrame h₁ = e₂.restrictFrame h₂) :
    (transition e₁ e₂ h₁ h₂ : Γ(X, W)) = a :=
  e₁.coord_eq h₁ ha

lemma transition_self (e : LocalFrame L V) {W : X.Opens} (h : W ≤ V) :
    transition e e h h = 1 :=
  Units.ext (transition_val_eq e e h h (one_smul _ _))

lemma transition_mul (e₁ : LocalFrame L V₁) (e₂ : LocalFrame L V₂) (e₃ : LocalFrame L V₃)
    {W : X.Opens} (h₁ : W ≤ V₁) (h₂ : W ≤ V₂) (h₃ : W ≤ V₃) :
    transition e₁ e₂ h₁ h₂ * transition e₂ e₃ h₂ h₃ = transition e₁ e₃ h₁ h₃ := by
  refine Units.ext (transition_val_eq e₁ e₃ h₁ h₃ ?_).symm
  rw [Units.val_mul, mul_comm, mul_smul, transition_smul, transition_smul]

lemma transition_inv (e₁ : LocalFrame L V₁) (e₂ : LocalFrame L V₂) {W : X.Opens}
    (h₁ : W ≤ V₁) (h₂ : W ≤ V₂) :
    (transition e₁ e₂ h₁ h₂)⁻¹ = transition e₂ e₁ h₂ h₁ := by
  rw [inv_eq_iff_mul_eq_one, transition_mul, transition_self]

/-- Restricting the transition unit to a smaller open gives the transition unit there. -/
lemma map_transition (e₁ : LocalFrame L V₁) (e₂ : LocalFrame L V₂) {W W' : X.Opens}
    (h₁ : W ≤ V₁) (h₂ : W ≤ V₂) (h : W' ≤ W) :
    Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom (transition e₁ e₂ h₁ h₂) =
      transition e₁ e₂ (h.trans h₁) (h.trans h₂) := by
  refine Units.ext (transition_val_eq e₁ e₂ _ _ ?_).symm
  rw [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
    ← e₁.restrictFrame_restrict h₁ h, ← e₂.restrictFrame_restrict h₂ h,
    ← transition_smul e₁ e₂ h₁ h₂, Scheme.Modules.map_smul]

lemma transition_restrict (e₁ : LocalFrame L V₁) (e₂ : LocalFrame L V₂) {W W₁ W₂ : X.Opens}
    (k₁ : W₁ ≤ V₁) (k₂ : W₂ ≤ V₂) (h₁ : W ≤ W₁) (h₂ : W ≤ W₂) :
    transition (e₁.restrict k₁) (e₂.restrict k₂) h₁ h₂ =
      transition e₁ e₂ (h₁.trans k₁) (h₂.trans k₂) := by
  refine Units.ext (transition_val_eq _ _ _ _ ?_)
  rw [restrict_restrictFrame, restrict_restrictFrame, transition_smul]

section OfIso

open Langlands.SchemeModule.SectionClearing

/-- A trivializing isomorphism onto the structure sheaf, as an isomorphism onto
`structureSheaf`. -/
abbrev structureIso (τ : L.obj.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf) :
    L.obj.restrict V.ι ≅ Langlands.Scheme.Modules.structureSheaf V.toScheme :=
  τ

private lemma chartE_smul_chartF
    (τ : L.obj.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)
    {W : X.Opens} (h : W ≤ V) (a : Γ(X, W)) :
    chartE (structureIso τ) W h
      (a • L.obj.presheaf.map (homOfLE h).op (chartF (structureIso τ) V le_rfl 1)) = a := by
  rw [chartE_smul, chartE_res (structureIso τ) V W le_rfl h, chartE_chartF, map_one, mul_one]

/-- The frame `τ⁻¹(1)` of an isomorphism `τ` trivializing `L` on `V`. -/
def ofIso (τ : L.obj.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf) :
    LocalFrame L V where
  frame := chartF (structureIso τ) V le_rfl 1
  bijective W h := by
    have hinj : Function.Injective (chartE (structureIso τ) W h) :=
      Function.LeftInverse.injective (chartF_chartE (structureIso τ) W h)
    refine Function.bijective_iff_has_inverse.mpr
      ⟨chartE (structureIso τ) W h, chartE_smul_chartF τ h, fun s => ?_⟩
    exact hinj (chartE_smul_chartF τ h (chartE (structureIso τ) W h s))

/-- The coordinates of the frame of `τ` are the chart coordinates of `τ`. -/
lemma ofIso_coord (τ : L.obj.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)
    {W : X.Opens} (h : W ≤ V) (s : Γ(L.obj, W)) :
    (ofIso τ).coord h s = chartE (structureIso τ) W h s := by
  refine (ofIso τ).coord_eq h ?_
  refine Function.LeftInverse.injective (chartF_chartE (structureIso τ) W h) ?_
  exact chartE_smul_chartF τ h _

end OfIso

end LocalFrame

end Frames

namespace RelativeForms

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- The logarithmic differential `u⁻¹ du` of a unit. -/
def dlog (u : Aˣ) : Ω[A⁄R] := ((u⁻¹ : Aˣ) : A) • KaehlerDifferential.D R A u

lemma dlog_mul (u v : Aˣ) : dlog (R := R) (u * v) = dlog u + dlog v := by
  have h₁ : ((u⁻¹ : Aˣ) : A) * ((v⁻¹ : Aˣ) : A) * u = ((v⁻¹ : Aˣ) : A) := by
    rw [mul_right_comm, Units.inv_mul, one_mul]
  have h₂ : ((u⁻¹ : Aˣ) : A) * ((v⁻¹ : Aˣ) : A) * v = ((u⁻¹ : Aˣ) : A) := by
    rw [mul_assoc, Units.inv_mul, mul_one]
  rw [dlog, dlog, dlog, mul_inv, Units.val_mul, Units.val_mul, Derivation.leibniz, smul_add,
    smul_smul, smul_smul, h₁, h₂, add_comm]

@[simp]
lemma dlog_one : dlog (R := R) (1 : Aˣ) = 0 := by
  simp [dlog]

lemma dlog_inv (u : Aˣ) : dlog (R := R) u⁻¹ = -dlog u :=
  eq_neg_of_add_eq_zero_left (by rw [← dlog_mul, inv_mul_cancel, dlog_one])

/-- Logarithmic differentials are natural in algebra homomorphisms. -/
lemma mapOne_dlog (φ : A →ₐ[R] B) (u : Aˣ) :
    mapOne φ (dlog u) = dlog (R := R) (Units.map φ.toRingHom.toMonoidHom u) := by
  rw [dlog, dlog, LinearMap.map_smulₛₗ, mapOne_d, Units.coe_map_inv, Units.coe_map]
  rfl

/-- Logarithmic differentials are closed. -/
@[simp]
lemma dOne_dlog (u : Aˣ) : dOne R A (dlog u) = 0 := by
  rw [dlog, dOne_smul_d,
    (KaehlerDifferential.D R A).leibniz_of_mul_eq_one (Units.inv_mul u)]
  change exteriorPower.ιMulti A 2 ![_ • KaehlerDifferential.D R A u,
    KaehlerDifferential.D R A u] = 0
  rw [(exteriorPower.ιMulti A 2).map_vecCons_smul]
  rw [(exteriorPower.ιMulti A 2).map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide),
    smul_zero]

end RelativeForms

section Cocycle

open Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq (inter inter_le_comp inter_le_apply)
open RelativeForms

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  (U : Scheme.AffineOpenCover.{u} X) (L : LineBundle X)

/-- A unit of the ring of functions on an open, as a unit of the section algebra. -/
def sectionUnit {W : X.Opens} (g : Γ(X, W)ˣ) : ((sectionAlgebras f).obj (op W))ˣ := g

/-- The logarithmic differential of a unit of the section ring of an open, in `oneForms`. -/
def dlogSection {W : X.Opens} (g : Γ(X, W)ˣ) : (oneForms f).obj (op W) :=
  dlog (R := R) (sectionUnit f g)

/-- Restriction of a logarithmic differential is the logarithmic differential of the
restricted unit. -/
lemma oneForms_map_dlogSection {W W' : X.Opens} (h : W' ≤ W) (g : Γ(X, W)ˣ) :
    (oneForms f).map (homOfLE h).op (dlogSection f g) =
      dlogSection f (Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom g) := by
  change mapOne ((sectionAlgebras f).map (homOfLE h).op).hom (dlogSection f g) = _
  rw [dlogSection, dlogSection, mapOne_dlog]
  rfl

/-- The exterior derivative of a logarithmic differential vanishes. -/
@[simp]
lemma exteriorD1_dlogSection {W : X.Opens} (g : Γ(X, W)ˣ) :
    (exteriorD1 f).app (op W) (dlogSection f g) = 0 :=
  dOne_dlog (R := R) (sectionUnit f g)

lemma dlogSection_mul {W : X.Opens} (g h : Γ(X, W)ˣ) :
    dlogSection f (g * h) = dlogSection f g + dlogSection f h :=
  dlog_mul (R := R) (sectionUnit f g) (sectionUnit f h)

lemma dlogSection_inv {W : X.Opens} (g : Γ(X, W)ˣ) :
    dlogSection f g⁻¹ = -dlogSection f g :=
  dlog_inv (R := R) (sectionUnit f g)

/-- Local trivializations of `L` on all members of the cover, given by frames. -/
abbrev CoverTrivialization := ∀ i : U.I₀, LocalFrame L (coverOpens U i)

variable {U L}

/-- The frames of isomorphisms trivializing `L` on the members of the cover. -/
def CoverTrivialization.ofIsos
    (τ : ∀ i : U.I₀, L.obj.restrict (coverOpens U i).ι ≅
      SheafOfModules.unit (coverOpens U i).toScheme.ringCatSheaf) :
    CoverTrivialization U L :=
  fun i => LocalFrame.ofIso (τ i)

/-- On the intersection of a tuple, the transition unit from the frame of `e` at the vertex
`a` to the frame of `e'` at the vertex `b`. -/
def tupleTransition (e e' : CoverTrivialization U L) {n : ℕ} (τ : Fin n → U.I₀) (a b : Fin n) :
    Γ(X, inter (coverOpens U) τ)ˣ :=
  LocalFrame.transition (e (τ a)) (e' (τ b)) (inter_le_apply τ a) (inter_le_apply τ b)

lemma tupleTransition_smul (e e' : CoverTrivialization U L) {n : ℕ} (τ : Fin n → U.I₀)
    (a b : Fin n) :
    (tupleTransition e e' τ a b : Γ(X, inter (coverOpens U) τ)) •
        (e (τ a)).restrictFrame (inter_le_apply τ a) =
      (e' (τ b)).restrictFrame (inter_le_apply τ b) :=
  LocalFrame.transition_smul _ _ _ _

lemma tupleTransition_mul (e e' e'' : CoverTrivialization U L) {n : ℕ} (τ : Fin n → U.I₀)
    (a b c : Fin n) :
    tupleTransition e e' τ a b * tupleTransition e' e'' τ b c = tupleTransition e e'' τ a c :=
  LocalFrame.transition_mul _ _ _ _ _ _

lemma tupleTransition_inv (e e' : CoverTrivialization U L) {n : ℕ} (τ : Fin n → U.I₀)
    (a b : Fin n) : (tupleTransition e e' τ a b)⁻¹ = tupleTransition e' e τ b a :=
  LocalFrame.transition_inv _ _ _ _

/-- Restricting from the intersection of a subtuple to the full intersection. -/
lemma map_tupleTransition (e e' : CoverTrivialization U L) {m n : ℕ} (τ : Fin n → U.I₀)
    (θ : Fin m → Fin n) (a b : Fin m) :
    Units.map (X.presheaf.map (homOfLE (inter_le_comp (U := coverOpens U) τ θ)).op).hom.toMonoidHom
        (tupleTransition e e' (τ ∘ θ) a b) =
      tupleTransition e e' τ (θ a) (θ b) :=
  LocalFrame.map_transition _ _ _ _ _

/-- The transition unit `g_σ` on `U_{σ 0} ∩ U_{σ 1}`, with `e_{σ 1} = g_σ • e_{σ 0}`. -/
abbrev transitionUnit (e : CoverTrivialization U L) (σ : Fin (1 + 1) → U.I₀) :
    Γ(X, inter (coverOpens U) σ)ˣ :=
  tupleTransition e e σ 0 1

/-- For trivializing isomorphisms `τ`, the transition unit is the `τ_{σ 0}`-coordinate of the
frame `τ_{σ 1}⁻¹(1)`. -/
lemma transitionUnit_ofIsos
    (τ : ∀ i : U.I₀, L.obj.restrict (coverOpens U i).ι ≅
      SheafOfModules.unit (coverOpens U i).toScheme.ringCatSheaf)
    (σ : Fin (1 + 1) → U.I₀) :
    (transitionUnit (CoverTrivialization.ofIsos τ) σ : Γ(X, inter (coverOpens U) σ)) =
      Langlands.SchemeModule.SectionClearing.chartE (LocalFrame.structureIso (τ (σ 0))) _
        (inter_le_apply σ 0) (L.obj.presheaf.map (homOfLE (inter_le_apply σ 1)).op
          (Langlands.SchemeModule.SectionClearing.chartF (LocalFrame.structureIso (τ (σ 1)))
            _ le_rfl 1)) :=
  LocalFrame.ofIso_coord _ _ _

/-- The transition unit of a constant pair is `1`. -/
lemma transitionUnit_const (e : CoverTrivialization U L) (i : U.I₀) :
    transitionUnit e (fun _ => i) = 1 :=
  LocalFrame.transition_self _ _

/-- The transition units form a multiplicative Čech cocycle for the face convention of
`cechD`: on a triple overlap the restrictions satisfy `g_{01} g_{12} = g_{02}`. -/
theorem transitionUnit_cocycle (e : CoverTrivialization U L) (τ : Fin (2 + 1) → U.I₀) :
    Units.map (X.presheaf.map (homOfLE (inter_le_comp (U := coverOpens U) τ
        (2 : Fin (2 + 1)).succAbove)).op).hom.toMonoidHom
        (transitionUnit e (τ ∘ (2 : Fin (2 + 1)).succAbove)) *
      Units.map (X.presheaf.map (homOfLE (inter_le_comp (U := coverOpens U) τ
        (0 : Fin (2 + 1)).succAbove)).op).hom.toMonoidHom
        (transitionUnit e (τ ∘ (0 : Fin (2 + 1)).succAbove)) =
    Units.map (X.presheaf.map (homOfLE (inter_le_comp (U := coverOpens U) τ
        (1 : Fin (2 + 1)).succAbove)).op).hom.toMonoidHom
        (transitionUnit e (τ ∘ (1 : Fin (2 + 1)).succAbove)) := by
  rw [transitionUnit, transitionUnit, transitionUnit, map_tupleTransition, map_tupleTransition,
    map_tupleTransition]
  exact tupleTransition_mul e e e τ 0 1 2

/-- If the frames change by `e'_i = u_i • e_i`, the transition units change by
`g'_σ = u_{σ 0}⁻¹ g_σ u_{σ 1}`, with `u_{σ a}` restricted to the pair overlap. -/
lemma transitionUnit_change (e e' : CoverTrivialization U L) (σ : Fin (1 + 1) → U.I₀) :
    transitionUnit e' σ =
      (tupleTransition e e' σ 0 0)⁻¹ * transitionUnit e σ * tupleTransition e e' σ 1 1 := by
  rw [tupleTransition_inv, transitionUnit, transitionUnit, tupleTransition_mul,
    tupleTransition_mul]

/-- The chart unit `u_i` of a change of frames `e'_i = u_i • e_i`, restricted to an
intersection containing the chart, is the tuple transition between the two frames. -/
lemma map_chartChange (e e' : CoverTrivialization U L) {n : ℕ} (τ : Fin n → U.I₀)
    (a : Fin n) :
    Units.map (X.presheaf.map (homOfLE (inter_le_comp (U := coverOpens U) τ
        (fun _ : Fin (0 + 1) => a))).op).hom.toMonoidHom
        (tupleTransition e e' (τ ∘ fun _ : Fin (0 + 1) => a) 0 0) =
      tupleTransition e e' τ a a :=
  map_tupleTransition e e' τ _ 0 0

variable (U L)

/-- The first Chern cocycle in total degree two: zero function cochain, the logarithmic
differentials `g_σ⁻¹ dg_σ` of the transition units on overlaps, and zero two-forms. -/
def firstChernCocycle (e : CoverTrivialization U L) : C2 f U :=
  (0, fun σ => dlogSection f (transitionUnit e σ), 0)

variable {U L}

@[simp]
lemma firstChernCocycle_fst (e : CoverTrivialization U L) :
    (firstChernCocycle f U L e).1 = 0 := rfl

@[simp]
lemma firstChernCocycle_snd_fst (e : CoverTrivialization U L) (σ : Fin (1 + 1) → U.I₀) :
    (firstChernCocycle f U L e).2.1 σ = dlogSection f (transitionUnit e σ) := rfl

@[simp]
lemma firstChernCocycle_snd_snd (e : CoverTrivialization U L) :
    (firstChernCocycle f U L e).2.2 = 0 := rfl

/-- Restriction of the logarithmic differential of a tuple transition. -/
private lemma oneForms_map_tupleTransition (e e' : CoverTrivialization U L) {m n : ℕ}
    (τ : Fin n → U.I₀) (θ : Fin m → Fin n) (a b : Fin m) :
    (oneForms f).map (homOfLE (inter_le_comp (U := coverOpens U) τ θ)).op
        (dlogSection f (tupleTransition e e' (τ ∘ θ) a b)) =
      dlogSection f (tupleTransition e e' τ (θ a) (θ b)) := by
  rw [oneForms_map_dlogSection, map_tupleTransition]

/-- The Čech closure equation `∂(g⁻¹ dg) = 0` on triple overlaps. -/
theorem cechD_firstChernCocycle (e : CoverTrivialization U L) :
    cechD U (oneForms f) 1 (firstChernCocycle f U L e).2.1 = 0 := by
  funext τ
  rw [cechD_apply, Fin.sum_univ_three]
  simp only [firstChernCocycle_snd_fst, transitionUnit, oneForms_map_tupleTransition]
  have h₀ : ((0 : Fin (1 + 2)).succAbove 0, (0 : Fin (1 + 2)).succAbove 1) = (1, 2) := rfl
  have h₁ : ((1 : Fin (1 + 2)).succAbove 0, (1 : Fin (1 + 2)).succAbove 1) = (0, 2) := rfl
  have h₂ : ((2 : Fin (1 + 2)).succAbove 0, (2 : Fin (1 + 2)).succAbove 1) = (0, 1) := rfl
  rw [Prod.mk.injEq] at h₀ h₁ h₂
  rw [h₀.1, h₀.2, h₁.1, h₁.2, h₂.1, h₂.2, ← tupleTransition_mul e e e τ 0 1 2,
    dlogSection_mul]
  change (1 : ℤ) • _ + (-1 : ℤ) • _ + (1 : ℤ) • _ = (0 : (oneForms f).obj _)
  rw [one_smul, one_smul, neg_one_smul]
  abel

/-- The exterior closure equation `d(g⁻¹ dg) = 0` on overlaps. -/
theorem exteriorD1_firstChernCocycle (e : CoverTrivialization U L) :
    cochainMap U (exteriorD1 f) 1 (firstChernCocycle f U L e).2.1 = 0 := by
  funext σ
  rw [cochainMap_apply, firstChernCocycle_snd_fst, exteriorD1_dlogSection]
  rfl

/-! ### Changing the trivializations on the same cover -/

/-- For a second family of frames `e'_i = u_i • e_i`, the degree-one cochain with zero
function component and the logarithmic differentials `u_i⁻¹ du_i` on the charts. -/
def frameChangeCochain (e e' : CoverTrivialization U L) : C1 f U :=
  (0, fun σ => dlogSection f (tupleTransition e e' σ 0 0))

/-- Changing the frames on the same cover changes the first Chern cocycle by the total
boundary `D1 (0, (u_i⁻¹ du_i)_i)`. -/
theorem firstChernCocycle_change (e e' : CoverTrivialization U L) :
    firstChernCocycle f U L e' =
      firstChernCocycle f U L e + D1 f U (frameChangeCochain f e e') := by
  rw [D1_apply]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change (0 : Cochains U (functions f) 2) = 0 + cechD U (functions f) 1 0
    rw [map_zero, add_zero]
  · funext σ
    change dlogSection f (tupleTransition e' e' σ 0 1) =
      dlogSection f (tupleTransition e e σ 0 1) +
        (cechD U (oneForms f) 0 (fun τ => dlogSection f (tupleTransition e e' τ 0 0)) σ -
          cochainMap U (exteriorD0 f) 1 0 σ)
    rw [map_zero, Pi.zero_apply, sub_zero, cechD_apply, Fin.sum_univ_two]
    simp only [oneForms_map_tupleTransition]
    have h₀ : (0 : Fin (0 + 2)).succAbove 0 = 1 := rfl
    have h₁ : (1 : Fin (0 + 2)).succAbove 0 = 0 := rfl
    rw [h₀, h₁, ← tupleTransition_mul e' e e' σ 0 1 1, ← tupleTransition_mul e' e e σ 0 0 1,
      ← tupleTransition_inv e e' σ 0 0, dlogSection_mul, dlogSection_mul, dlogSection_inv]
    change _ = _ + ((1 : ℤ) • _ + (-1 : ℤ) • _)
    rw [one_smul, neg_one_smul]
    abel
  · funext σ
    change (0 : (twoForms f).obj _) = 0 +
      (exteriorD1 f).app _ (dlogSection f (tupleTransition e e' σ 0 0))
    rw [exteriorD1_dlogSection, add_zero]

/-- The difference of the first Chern cocycles of two families of frames on the same cover
is a total boundary. -/
theorem firstChernCocycle_sub_mem_range_D1 (e e' : CoverTrivialization U L) :
    firstChernCocycle f U L e' - firstChernCocycle f U L e ∈ LinearMap.range (D1 f U) :=
  ⟨frameChangeCochain f e e', by rw [firstChernCocycle_change f e e', add_sub_cancel_left]⟩

/-! ### Restriction to a refinement -/

section Refinement

variable {V : Scheme.AffineOpenCover.{u} X} {β : V.I₀ → U.I₀}

lemma inter_le_refine (hβ : ∀ k, coverOpens V k ≤ coverOpens U (β k)) {n : ℕ}
    (σ : Fin n → V.I₀) : inter (coverOpens V) σ ≤ inter (coverOpens U) (β ∘ σ) :=
  le_iInf fun a => (inter_le_apply σ a).trans (hβ (σ a))

variable (hβ : ∀ k, coverOpens V k ≤ coverOpens U (β k))

/-- Restriction of Čech cochains to a refinement `V_k ⊆ U_{β k}`. -/
def refineCochains (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R) (p : ℕ) :
    Cochains U P p →ₗ[R] Cochains V P p :=
  LinearMap.pi fun σ =>
    (P.map (homOfLE (inter_le_refine hβ σ)).op).hom.comp (LinearMap.proj (β ∘ σ))

@[simp]
lemma refineCochains_apply (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R) (p : ℕ) (c : Cochains U P p)
    (σ : Fin (p + 1) → V.I₀) :
    refineCochains hβ P p c σ = P.map (homOfLE (inter_le_refine hβ σ)).op (c (β ∘ σ)) := rfl

/-- Restriction of total degree-two cochains to a refinement, componentwise. -/
def refineC2 : C2 f U →ₗ[R] C2 f V :=
  (refineCochains hβ (functions f) 2).prodMap
    ((refineCochains hβ (oneForms f) 1).prodMap (refineCochains hβ (twoForms f) 0))

/-- The restrictions of the frames to the members of a refinement. -/
def CoverTrivialization.restrictRefinement (e : CoverTrivialization U L) :
    CoverTrivialization V L :=
  fun k => (e (β k)).restrict (hβ k)

/-- Restricting the frames to a refinement restricts the first Chern cocycle. -/
theorem firstChernCocycle_restrictRefinement (e : CoverTrivialization U L) :
    firstChernCocycle f V L (CoverTrivialization.restrictRefinement hβ e) =
      refineC2 f hβ (firstChernCocycle f U L e) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change (0 : Cochains V (functions f) 2) = refineCochains hβ (functions f) 2 0
    rw [map_zero]
  · funext σ
    change dlogSection f (transitionUnit (CoverTrivialization.restrictRefinement hβ e) σ) =
      (oneForms f).map (homOfLE (inter_le_refine hβ σ)).op
        (dlogSection f (transitionUnit e (β ∘ σ)))
    rw [oneForms_map_dlogSection, transitionUnit, transitionUnit, tupleTransition,
      tupleTransition, LocalFrame.map_transition]
    exact congrArg (dlogSection f) (LocalFrame.transition_restrict _ _ _ _ _ _)
  · change (0 : Cochains V (twoForms f) 0) = refineCochains hβ (twoForms f) 0 0
    rw [map_zero]

end Refinement

end Cocycle

/-! ### The Poincaré line bundle -/

section Poincare

open Langlands.AbelianScheme

variable {R : Type u} [CommRing R] (A : AbelianScheme (Spec (CommRingCat.of R)))
  (hA : HasDualScheme A)

/-- The structure morphism of the total space `A ×_S A^∨` of the Poincaré bundle to
`S = Spec R`. -/
abbrev poincareStructureMorphism :
    ((baseChange (dualScheme A hA).hom).obj A).X.left ⟶ Spec (CommRingCat.of R) :=
  ((baseChange (dualScheme A hA).hom).obj A).X.hom ≫ (dualScheme A hA).hom

/-- The first Chern cocycle of the Poincaré line bundle for a supplied affine cover of
`A ×_S A^∨` with frames. -/
abbrev poincareFirstChernCocycle
    (U : Scheme.AffineOpenCover.{u} ((baseChange (dualScheme A hA).hom).obj A).X.left)
    (e : CoverTrivialization U (poincareLineBundle A hA)) :
    C2 (poincareStructureMorphism A hA) U :=
  firstChernCocycle (poincareStructureMorphism A hA) U (poincareLineBundle A hA) e

/-- The Čech and exterior closure equations for the Poincaré first Chern cocycle. -/
theorem poincareFirstChernCocycle_closed
    (U : Scheme.AffineOpenCover.{u} ((baseChange (dualScheme A hA).hom).obj A).X.left)
    (e : CoverTrivialization U (poincareLineBundle A hA)) :
    cechD U (oneForms (poincareStructureMorphism A hA)) 1
        (poincareFirstChernCocycle A hA U e).2.1 = 0 ∧
      cochainMap U (exteriorD1 (poincareStructureMorphism A hA)) 1
        (poincareFirstChernCocycle A hA U e).2.1 = 0 :=
  ⟨cechD_firstChernCocycle _ e, exteriorD1_firstChernCocycle _ e⟩

end Poincare

end Langlands.AlgebraicGeometry.AffineCechDeRham
