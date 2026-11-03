import Langlands.GroupScheme.Dynamic.FlagQuotientTranslations

/-! # The actual left action on a scheme coset quotient -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}} (G : GroupScheme S)
variable (H : SubgroupFunctor G) {Q : Over S} (q : G.X ⟶ Q)
variable (hfib : ∀ (T : Over S) (g h : T ⟶ G.X),
  g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ H.carrier T)

include hfib

/-- Multiplication followed by the quotient is constant on the fibers of
the product of the identity with the quotient. -/
theorem flagQuotientMultiplication_preserves_fibers {T : Over S}
    (f f' : T ⟶ G.X ⊗ G.X) (he : f ≫ (G.X ◁ q) = f' ≫ (G.X ◁ q)) :
    f ≫ μ[G.X] ≫ q = f' ≫ μ[G.X] ≫ q := by
  have ha := congrArg (fun e => e ≫ fst G.X Q) he
  have hb := congrArg (fun e => e ≫ snd G.X Q) he
  simp only [Category.assoc, whiskerLeft_fst] at ha
  simp only [Category.assoc, whiskerLeft_snd] at hb
  have hm (e : T ⟶ G.X ⊗ G.X) :
      e ≫ μ[G.X] = (e ≫ fst _ _) * (e ≫ snd _ _) := by
    rw [Hom.mul_def, lift_comp_fst_snd]
  rw [← Category.assoc, ← Category.assoc, hm, hm]
  apply (hfib T _ _).mpr
  rw [ha]
  simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left] using
    (hfib T _ _).mp hb

/-- The same compatibility for arbitrary underlying scheme maps. -/
theorem flagQuotientMultiplication_preserves_scheme_fibers {T : Scheme.{u}}
    (f f' : T ⟶ (G.X ⊗ G.X).left)
    (he : f ≫ (G.X ◁ q).left = f' ≫ (G.X ◁ q).left) :
    f ≫ (μ[G.X] ≫ q).left = f' ≫ (μ[G.X] ≫ q).left := by
  have hb : f' ≫ (G.X ⊗ G.X).hom = f ≫ (G.X ⊗ G.X).hom := by
    rw [← Over.w (G.X ◁ q), ← Category.assoc, ← he, Category.assoc]
  let f₀ : Over.mk (f ≫ (G.X ⊗ G.X).hom) ⟶ G.X ⊗ G.X := Over.homMk f rfl
  let f₁ : Over.mk (f ≫ (G.X ⊗ G.X).hom) ⟶ G.X ⊗ G.X := Over.homMk f' hb
  exact congrArg (fun e => e.left)
    (flagQuotientMultiplication_preserves_fibers G H q hfib f₀ f₁
      (Over.OverMorphism.ext he))

omit hfib

private abbrev flagFpqcProperty : MorphismProperty Scheme.{u} :=
  @QuasiCompact ⊓ (@Flat ⊓ @Surjective)

variable [QuasiCompact q.left] [Flat q.left] [Surjective q.left]

set_option backward.isDefEq.respectTransparency false in
private theorem flagFpqc_whiskerLeft (T : Over S) :
    flagFpqcProperty (T ◁ q).left := by
  exact MorphismProperty.pullbackMap (P := flagFpqcProperty)
    (by change flagFpqcProperty (𝟙 T.left);
        exact ⟨inferInstance, inferInstance, inferInstance⟩)
    ⟨inferInstance, inferInstance, inferInstance⟩
    (by simp) (Over.w q).symm

/-- Product on the left preserves the effective epimorphism of an fpqc map. -/
theorem flagQuotient_effectiveEpi_whiskerLeft (T : Over S) :
    EffectiveEpi (T ◁ q).left := by
  obtain ⟨hq, hf, hs⟩ := flagFpqc_whiskerLeft G q T
  let : QuasiCompact (T ◁ q).left := hq
  let : Flat (T ◁ q).left := hf
  let : Surjective (T ◁ q).left := hs
  infer_instance

include hfib

/-- The actual scheme morphism descended from multiplication. -/
def flagQuotientActionSchemeHom : (G.X ⊗ Q).left ⟶ Q.left :=
  haveI := flagQuotient_effectiveEpi_whiskerLeft G q G.X
  EffectiveEpi.desc (G.X ◁ q).left (μ[G.X] ≫ q).left
    (fun f f' he => flagQuotientMultiplication_preserves_scheme_fibers G H q hfib f f' he)

@[reassoc]
theorem fac_flagQuotientActionSchemeHom :
    (G.X ◁ q).left ≫ flagQuotientActionSchemeHom G H q hfib = (μ[G.X] ≫ q).left :=
  haveI := flagQuotient_effectiveEpi_whiskerLeft G q G.X
  EffectiveEpi.fac _ _ _

/-- The descended action morphism over the same base scheme. -/
def flagQuotientActionHom : G.X ⊗ Q ⟶ Q :=
  Over.homMk (flagQuotientActionSchemeHom G H q hfib) (by
    have := flagQuotient_effectiveEpi_whiskerLeft G q G.X
    apply (cancel_epi (G.X ◁ q).left).mp
    rw [fac_flagQuotientActionSchemeHom_assoc, Over.w, Over.w])

@[reassoc]
theorem fac_flagQuotientActionHom :
    (G.X ◁ q) ≫ flagQuotientActionHom G H q hfib = μ[G.X] ≫ q :=
  Over.OverMorphism.ext (fac_flagQuotientActionSchemeHom G H q hfib)

/-- Evaluation of the actual action on any test scheme. -/
def flagQuotientAct {T : Over S} (g : T ⟶ G.X) (x : T ⟶ Q) : T ⟶ Q :=
  lift g x ≫ flagQuotientActionHom G H q hfib

/-- A lifted quotient point is acted on by multiplication in the original group. -/
theorem flagQuotientAct_lift {T : Over S} (g h : T ⟶ G.X) :
    flagQuotientAct G H q hfib g (h ≫ q) = (g * h) ≫ q := by
  rw [flagQuotientAct, ← lift_whiskerLeft, Category.assoc, fac_flagQuotientActionHom]
  rfl

/-- The action on test points is natural in the test scheme. -/
theorem flagQuotientAct_naturality {T V : Over S} (b : V ⟶ T)
    (g : T ⟶ G.X) (x : T ⟶ Q) :
    b ≫ flagQuotientAct G H q hfib g x =
      flagQuotientAct G H q hfib (b ≫ g) (b ≫ x) := by
  rw [flagQuotientAct, flagQuotientAct, ← Category.assoc, comp_lift]

omit hfib in
/-- Equality can be checked after pulling back the fpqc quotient along any test point. -/
theorem flagQuotient_hom_ext_of_local_lift {T Y : Over S} (x : T ⟶ Q)
    (f f' : T ⟶ Y)
    (he : ∀ (V : Over S) (b : V ⟶ T) (g : V ⟶ G.X),
      b ≫ x = g ≫ q → b ≫ f = b ≫ f') : f = f' := by
  let V : Over S := Over.mk (pullback.fst x.left q.left ≫ T.hom)
  let b : V ⟶ T := Over.homMk (pullback.fst x.left q.left) rfl
  let g : V ⟶ G.X := Over.homMk (pullback.snd x.left q.left) (by
    rw [← Over.w q, ← Category.assoc, ← pullback.condition, Category.assoc, Over.w x]
    rfl)
  have : Epi b.left := by
    change Epi (pullback.fst x.left q.left)
    infer_instance
  have : Epi b := Over.epi_of_epi_left b
  apply (cancel_epi b).mp
  exact he V b g (Over.OverMorphism.ext pullback.condition)

/-- The identity group point acts as the identity on every quotient point. -/
theorem flagQuotientAct_one {T : Over S} (x : T ⟶ Q) :
    flagQuotientAct G H q hfib 1 x = x := by
  apply flagQuotient_hom_ext_of_local_lift G q x
  intro V b g hb
  rw [flagQuotientAct_naturality, MonObj.comp_one, hb, flagQuotientAct_lift, one_mul]

/-- The actual action satisfies the multiplication law on every test scheme. -/
theorem flagQuotientAct_mul {T : Over S} (g h : T ⟶ G.X) (x : T ⟶ Q) :
    flagQuotientAct G H q hfib (g * h) x =
      flagQuotientAct G H q hfib g (flagQuotientAct G H q hfib h x) := by
  apply flagQuotient_hom_ext_of_local_lift G q x
  intro V b a hb
  rw [flagQuotientAct_naturality, flagQuotientAct_naturality,
    flagQuotientAct_naturality, MonObj.comp_mul, hb,
    flagQuotientAct_lift, flagQuotientAct_lift, flagQuotientAct_lift, mul_assoc]

/-- Acting by an inverse cancels an action, including for quotient points
which do not lift on the original test scheme. -/
theorem flagQuotientAct_inv_cancel {T : Over S} (g : T ⟶ G.X) (x : T ⟶ Q) :
    flagQuotientAct G H q hfib g⁻¹ (flagQuotientAct G H q hfib g x) = x := by
  rw [← flagQuotientAct_mul, inv_mul_cancel, flagQuotientAct_one]

end Langlands.GroupScheme.Dynamic
