import Langlands.GroupScheme.AutomorphicAction
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Descent of automorphic actions through fpqc homomorphisms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

variable {S : Scheme.{u}} {H Q G : GroupScheme S}

/-- The actual kernel acts trivially on every test scheme. -/
def KernelActsTrivially (a : AutomorphicAction H G) (q : H ⟶ Q) : Prop :=
  ∀ (T : Over S) (k : T ⟶ (kernel q).X) (g : T ⟶ G.X),
    (a.restrict (kernelι q)).act k g = g

/-- Automorphic actions are determined by their actual action morphism. -/
theorem ext_hom {b c : AutomorphicAction H G} (h : b.hom = c.hom) : b = c := by
  cases b
  cases c
  cases h
  rfl

/-- Restriction of any action makes the actual kernel act trivially. -/
theorem restrict_kernelActsTrivially (b : AutomorphicAction Q G) (q : H ⟶ Q) :
    (b.restrict q).KernelActsTrivially q := by
  intro T k g
  have he : (k ≫ (kernelι q).hom.hom) ≫ q.hom.hom = 1 :=
    (kernelPointsEquiv q T k).property
  simp only [restrict_act, he, b.act_one_left]

variable (a : AutomorphicAction H G) (q : H ⟶ Q) (hk : a.KernelActsTrivially q)

include hk

/-- Equal quotient images give identical actions, by division in the actual kernel. -/
theorem act_eq_of_quotient_eq {T : Over S} (h h' : T ⟶ H.X)
    (he : h ≫ q.hom.hom = h' ≫ q.hom.hom) (g : T ⟶ G.X) :
    a.act h g = a.act h' g := by
  have hd : (h / h') ≫ q.hom.hom = toUnit T ≫ η[Q.X] := by
    rw [GrpObj.div_comp, he, div_self']
    rfl
  let k := (kernel_isPullback q).lift (h / h') (toUnit T) hd
  have hki : k ≫ (kernelι q).hom.hom = h / h' :=
    (kernel_isPullback q).lift_fst _ _ _
  have e := hk T k (a.act h' g)
  rw [restrict_act, hki, ← a.act_mul_left, div_mul_cancel] at e
  exact e

/-- The action morphism coequalizes the relations of the quotient times the target. -/
theorem hom_comp_eq_of_quotient_eq {T : Over S} (f f' : T ⟶ H.X ⊗ G.X)
    (he : f ≫ (q.hom.hom ▷ G.X) = f' ≫ (q.hom.hom ▷ G.X)) :
    f ≫ a.hom = f' ≫ a.hom := by
  have hh := congrArg (fun x => x ≫ fst Q.X G.X) he
  have hg := congrArg (fun x => x ≫ snd Q.X G.X) he
  simp only [Category.assoc, whiskerRight_fst] at hh
  simp only [Category.assoc, whiskerRight_snd] at hg
  have e := act_eq_of_quotient_eq a q hk
    (f ≫ fst H.X G.X) (f' ≫ fst H.X G.X) hh (f ≫ snd H.X G.X)
  simp only [act] at e
  rw [lift_comp_fst_snd, hg, lift_comp_fst_snd] at e
  exact e

/-- The same relation statement for arbitrary maps of underlying schemes. -/
theorem schemeHom_comp_eq_of_quotient_eq {Z : Scheme.{u}}
    (f f' : Z ⟶ (H.X ⊗ G.X).left)
    (he : f ≫ (q.hom.hom ▷ G.X).left = f' ≫ (q.hom.hom ▷ G.X).left) :
    f ≫ a.hom.left = f' ≫ a.hom.left := by
  have hs : f' ≫ (H.X ⊗ G.X).hom = f ≫ (H.X ⊗ G.X).hom := by
    rw [← Over.w (q.hom.hom ▷ G.X), ← Category.assoc, ← he, Category.assoc]
  let f₀ : Over.mk (f ≫ (H.X ⊗ G.X).hom) ⟶ H.X ⊗ G.X := Over.homMk f rfl
  let f₁ : Over.mk (f ≫ (H.X ⊗ G.X).hom) ⟶ H.X ⊗ G.X := Over.homMk f' hs
  exact congrArg (fun x => x.left)
    (hom_comp_eq_of_quotient_eq a q hk f₀ f₁ (Over.OverMorphism.ext he))

omit hk

private abbrev fpqcProperty : MorphismProperty Scheme.{u} :=
  @QuasiCompact ⊓ (@Flat ⊓ @Surjective)

variable [QuasiCompact q.hom.hom.left] [Flat q.hom.hom.left] [Surjective q.hom.hom.left]

set_option backward.isDefEq.respectTransparency false in
private theorem fpqc_whiskerRight (T : Over S) :
    fpqcProperty (q.hom.hom ▷ T).left := by
  exact MorphismProperty.pullbackMap (P := fpqcProperty)
    ⟨inferInstance, inferInstance, inferInstance⟩
    (by change fpqcProperty (𝟙 T.left); exact ⟨inferInstance, inferInstance, inferInstance⟩)
    (Over.w q.hom.hom).symm (by simp)

/-- Product with a test scheme preserves the effective epimorphism used for descent. -/
theorem effectiveEpi_whiskerRight (T : Over S) :
    EffectiveEpi (q.hom.hom ▷ T).left := by
  obtain ⟨hq, hf, hs⟩ := fpqc_whiskerRight q T
  let : QuasiCompact (q.hom.hom ▷ T).left := hq
  let : Flat (q.hom.hom ▷ T).left := hf
  let : Surjective (q.hom.hom ▷ T).left := hs
  infer_instance

include hk

/-- Descend the actual action morphism as a map of schemes. -/
def quotientActionSchemeHom : (Q.X ⊗ G.X).left ⟶ G.X.left :=
  haveI := effectiveEpi_whiskerRight q G.X
  EffectiveEpi.desc (q.hom.hom ▷ G.X).left a.hom.left
    (fun f f' he => schemeHom_comp_eq_of_quotient_eq a q hk f f' he)

@[reassoc]
theorem fac_quotientActionSchemeHom :
    (q.hom.hom ▷ G.X).left ≫ quotientActionSchemeHom a q hk = a.hom.left :=
  haveI := effectiveEpi_whiskerRight q G.X
  EffectiveEpi.fac _ _ _

/-- The descended scheme morphism is over the original base. -/
def quotientActionHom : Q.X ⊗ G.X ⟶ G.X :=
  Over.homMk (quotientActionSchemeHom a q hk) (by
    have := effectiveEpi_whiskerRight q G.X
    apply (cancel_epi (q.hom.hom ▷ G.X).left).mp
    rw [fac_quotientActionSchemeHom_assoc, Over.w, Over.w])

@[reassoc]
theorem fac_quotientActionHom :
    (q.hom.hom ▷ G.X) ≫ quotientActionHom a q hk = a.hom :=
  Over.OverMorphism.ext (fac_quotientActionSchemeHom a q hk)

/-- The descended morphism recovers the action whenever an acting point lifts. -/
theorem lift_quotientActionHom {T : Over S} (h : T ⟶ H.X) (g : T ⟶ G.X) :
    lift (h ≫ q.hom.hom) g ≫ quotientActionHom a q hk = a.act h g := by
  rw [← lift_whiskerRight, Category.assoc, fac_quotientActionHom]
  rfl

/-- The descended morphism induces natural maps on all test schemes. -/
theorem quotientActionHom_naturality {T V : Over S} (b : V ⟶ T)
    (x : T ⟶ Q.X) (g : T ⟶ G.X) :
    b ≫ (lift x g ≫ quotientActionHom a q hk) =
      lift (b ≫ x) (b ≫ g) ≫ quotientActionHom a q hk := by
  rw [← Category.assoc, comp_lift]

omit hk

/-- Equality of maps out of a test scheme can be checked after locally lifting any
one of its quotient points along the fpqc morphism. -/
theorem hom_ext_of_local_quotient_lift {T Y : Over S} (x : T ⟶ Q.X)
    (f f' : T ⟶ Y)
    (he : ∀ (V : Over S) (b : V ⟶ T) (h : V ⟶ H.X),
      b ≫ x = h ≫ q.hom.hom → b ≫ f = b ≫ f') : f = f' := by
  let V : Over S := Over.mk (pullback.fst x.left q.hom.hom.left ≫ T.hom)
  let b : V ⟶ T := Over.homMk (pullback.fst x.left q.hom.hom.left) rfl
  let h : V ⟶ H.X := Over.homMk (pullback.snd x.left q.hom.hom.left) (by
    rw [← Over.w q.hom.hom, ← Category.assoc, ← pullback.condition,
      Category.assoc, Over.w x]
    rfl)
  have : Epi b.left := by
    change Epi (pullback.fst x.left q.hom.hom.left)
    infer_instance
  have : Epi b := Over.epi_of_epi_left b
  apply (cancel_epi b).mp
  exact he V b h (Over.OverMorphism.ext pullback.condition)

include hk

/-- The unique descended automorphic action through the given fpqc homomorphism.
Its laws can be checked after locally lifting acting points; the kernel may be
nonsmooth, and points need not lift on the original test scheme. -/
def quotientAction : AutomorphicAction Q G where
  hom := quotientActionHom a q hk
  one_left g := by
    simpa only [MonObj.one_comp] using
      (lift_quotientActionHom a q hk (1 : _ ⟶ H.X) g).trans (a.act_one_left g)
  mul_left x y g := by
    apply hom_ext_of_local_quotient_lift q x
    intro V b h hb
    rw [quotientActionHom_naturality, quotientActionHom_naturality,
      quotientActionHom_naturality, MonObj.comp_mul, hb]
    apply hom_ext_of_local_quotient_lift q (b ≫ y)
    intro W c k hc
    rw [quotientActionHom_naturality, quotientActionHom_naturality,
      quotientActionHom_naturality, MonObj.comp_mul, hc,
      ← Category.assoc, ← MonObj.mul_comp]
    rw [lift_quotientActionHom, lift_quotientActionHom, lift_quotientActionHom,
      a.act_mul_left]
  mul_right x g g' := by
    apply hom_ext_of_local_quotient_lift q x
    intro V b h hb
    simp only [quotientActionHom_naturality, MonObj.comp_mul, hb,
      lift_quotientActionHom, a.act_mul_right]

@[simp]
theorem quotientAction_act_lift {T : Over S} (h : T ⟶ H.X) (g : T ⟶ G.X) :
    (quotientAction a q hk).act (h ≫ q.hom.hom) g = a.act h g :=
  lift_quotientActionHom a q hk h g

/-- The descended action morphism restricts to the original action morphism. -/
theorem quotientAction_restrict_hom :
    ((quotientAction a q hk).restrict q).hom = a.hom :=
  fac_quotientActionHom a q hk

/-- The action morphism is uniquely determined by its restriction along the
given fpqc homomorphism. -/
theorem quotientAction_hom_unique (b : AutomorphicAction Q G)
    (hb : (b.restrict q).hom = a.hom) :
    b.hom = (quotientAction a q hk).hom := by
  have := effectiveEpi_whiskerRight q G.X
  apply Over.OverMorphism.ext
  apply (cancel_epi (q.hom.hom ▷ G.X).left).mp
  exact congrArg (fun f => f.left) (hb.trans (quotientAction_restrict_hom a q hk).symm)

@[simp]
theorem quotientAction_restrict : (quotientAction a q hk).restrict q = a :=
  ext_hom (quotientAction_restrict_hom a q hk)

/-- Uniqueness as a bundled automorphic action. -/
theorem quotientAction_unique (b : AutomorphicAction Q G) (hb : b.restrict q = a) :
    b = quotientAction a q hk :=
  ext_hom (quotientAction_hom_unique a q hk b (congrArg AutomorphicAction.hom hb))

omit hk in
/-- Kernel triviality is exactly the condition for descent of an automorphic
action through the specified fpqc homomorphism. -/
theorem exists_quotientAction_iff :
    (∃ b : AutomorphicAction Q G, b.restrict q = a) ↔ a.KernelActsTrivially q := by
  constructor
  · rintro ⟨b, rfl⟩
    exact restrict_kernelActsTrivially b q
  · intro hk
    exact ⟨quotientAction a q hk, quotientAction_restrict a q hk⟩

end Langlands.GroupScheme.AutomorphicAction
