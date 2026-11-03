import Langlands.GroupScheme.ActionDescent
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Dynamic.ActionFunctoriality
import Langlands.GroupScheme.Dynamic.FlagQuotientAction
import Langlands.GroupScheme.RepresentedAction

/-! # Automorphic actions on fpqc quotient group schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

variable {S : Scheme.{u}} {H G Q : GroupScheme S}
variable (a : AutomorphicAction H G) (q : G ⟶ Q)
variable (hk : a.IsStable (SubgroupFunctor.range (kernelι q)))

include hk

/-- A stable actual kernel makes the image of the action depend only on the
quotient image of the acted-on point, on every test scheme. -/
theorem act_comp_eq_of_comp_eq {T : Over S} (h : T ⟶ H.X) (g g' : T ⟶ G.X)
    (he : g ≫ q.hom.hom = g' ≫ q.hom.hom) :
    a.act h g ≫ q.hom.hom = a.act h g' ≫ q.hom.hom := by
  have hd : (g / g') ≫ q.hom.hom = 1 := by
    rw [GrpObj.div_comp, he, div_self']
  have ha := (mem_range_kernelι_iff q (a.act h (g / g'))).mp
    (hk T h (g / g') ((mem_range_kernelι_iff q (g / g')).mpr hd))
  have hdiv : a.act h (g / g') = a.act h g / a.act h g' :=
    (a.pointAut T h).map_div g g'
  rw [hdiv, GrpObj.div_comp] at ha
  exact div_eq_one.mp ha

/-- The action followed by the quotient coequalizes the fibers of the product
of the acting scheme with the given quotient map. -/
theorem action_comp_preserves_quotient_fibers {T : Over S}
    (f f' : T ⟶ H.X ⊗ G.X)
    (he : f ≫ (H.X ◁ q.hom.hom) = f' ≫ (H.X ◁ q.hom.hom)) :
    f ≫ a.hom ≫ q.hom.hom = f' ≫ a.hom ≫ q.hom.hom := by
  have hh := congrArg (fun x => x ≫ fst H.X Q.X) he
  have hg := congrArg (fun x => x ≫ snd H.X Q.X) he
  simp only [Category.assoc, whiskerLeft_fst] at hh
  simp only [Category.assoc, whiskerLeft_snd] at hg
  have e := act_comp_eq_of_comp_eq a q hk
    (f ≫ fst H.X G.X) (f ≫ snd H.X G.X) (f' ≫ snd H.X G.X) hg
  simp only [act] at e
  rw [lift_comp_fst_snd, hh, lift_comp_fst_snd] at e
  exact e

/-- The same relation for arbitrary maps of the underlying schemes. -/
theorem action_comp_preserves_quotient_scheme_fibers {Z : Scheme.{u}}
    (f f' : Z ⟶ (H.X ⊗ G.X).left)
    (he : f ≫ (H.X ◁ q.hom.hom).left = f' ≫ (H.X ◁ q.hom.hom).left) :
    f ≫ (a.hom ≫ q.hom.hom).left = f' ≫ (a.hom ≫ q.hom.hom).left := by
  have hs : f' ≫ (H.X ⊗ G.X).hom = f ≫ (H.X ⊗ G.X).hom := by
    rw [← Over.w (H.X ◁ q.hom.hom), ← Category.assoc, ← he, Category.assoc]
  let f₀ : Over.mk (f ≫ (H.X ⊗ G.X).hom) ⟶ H.X ⊗ G.X := Over.homMk f rfl
  let f₁ : Over.mk (f ≫ (H.X ⊗ G.X).hom) ⟶ H.X ⊗ G.X := Over.homMk f' hs
  exact congrArg (fun x => x.left)
    (action_comp_preserves_quotient_fibers a q hk f₀ f₁ (Over.OverMorphism.ext he))

omit hk in
/-- Any action making a homomorphism equivariant preserves its actual kernel. -/
theorem isStable_kernel_of_equivariant (b : AutomorphicAction H Q)
    (hb : a.IsEquivariant b q) : a.IsStable (SubgroupFunctor.range (kernelι q)) := by
  intro T h g hg
  apply (mem_range_kernelι_iff q (a.act h g)).mpr
  rw [hb, (mem_range_kernelι_iff q g).mp hg, b.act_one]

variable [QuasiCompact q.hom.hom.left] [Flat q.hom.hom.left] [Surjective q.hom.hom.left]

/-- Descend the action followed by the quotient as an actual scheme morphism. -/
def onQuotientSchemeHom : (H.X ⊗ Q.X).left ⟶ Q.X.left :=
  haveI := Dynamic.flagQuotient_effectiveEpi_whiskerLeft G q.hom.hom H.X
  EffectiveEpi.desc (H.X ◁ q.hom.hom).left (a.hom ≫ q.hom.hom).left
    (fun f f' he => action_comp_preserves_quotient_scheme_fibers a q hk f f' he)

@[reassoc]
theorem fac_onQuotientSchemeHom :
    (H.X ◁ q.hom.hom).left ≫ onQuotientSchemeHom a q hk =
      (a.hom ≫ q.hom.hom).left :=
  haveI := Dynamic.flagQuotient_effectiveEpi_whiskerLeft G q.hom.hom H.X
  EffectiveEpi.fac _ _ _

/-- The descended action morphism lies over the original base. -/
def onQuotientHom : H.X ⊗ Q.X ⟶ Q.X :=
  Over.homMk (onQuotientSchemeHom a q hk) (by
    have := Dynamic.flagQuotient_effectiveEpi_whiskerLeft G q.hom.hom H.X
    apply (cancel_epi (H.X ◁ q.hom.hom).left).mp
    rw [fac_onQuotientSchemeHom_assoc, Over.w, Over.w])

@[reassoc]
theorem fac_onQuotientHom :
    (H.X ◁ q.hom.hom) ≫ onQuotientHom a q hk = a.hom ≫ q.hom.hom :=
  Over.OverMorphism.ext (fac_onQuotientSchemeHom a q hk)

/-- Evaluate the descended morphism at a quotient point with a chosen lift. -/
theorem lift_onQuotientHom {T : Over S} (h : T ⟶ H.X) (g : T ⟶ G.X) :
    lift h (g ≫ q.hom.hom) ≫ onQuotientHom a q hk = a.act h g ≫ q.hom.hom := by
  rw [← lift_whiskerLeft, Category.assoc, fac_onQuotientHom]
  rfl

/-- Evaluation is natural under arbitrary refinements of a test scheme. -/
theorem onQuotientHom_naturality {T V : Over S} (b : V ⟶ T)
    (h : T ⟶ H.X) (x : T ⟶ Q.X) :
    b ≫ (lift h x ≫ onQuotientHom a q hk) =
      lift (b ≫ h) (b ≫ x) ≫ onQuotientHom a q hk := by
  rw [← Category.assoc, comp_lift]

/-- The automorphic action on a specified fpqc quotient with stable actual
kernel. Laws hold on every test, including points without a global lift. -/
def onQuotient : AutomorphicAction H Q where
  hom := onQuotientHom a q hk
  one_left x := by
    apply hom_ext_of_local_quotient_lift q x
    intro V b g hb
    rw [onQuotientHom_naturality, MonObj.comp_one, hb, lift_onQuotientHom,
      a.act_one_left]
  mul_left h h' x := by
    apply hom_ext_of_local_quotient_lift q x
    intro V b g hb
    rw [onQuotientHom_naturality, onQuotientHom_naturality,
      onQuotientHom_naturality, MonObj.comp_mul, hb,
      lift_onQuotientHom, lift_onQuotientHom, lift_onQuotientHom, a.act_mul_left]
  mul_right h x y := by
    apply hom_ext_of_local_quotient_lift q x
    intro V b g hb
    simp only [onQuotientHom_naturality, MonObj.comp_mul, hb]
    apply hom_ext_of_local_quotient_lift q (b ≫ y)
    intro W c g' hc
    simp only [onQuotientHom_naturality, MonObj.comp_mul, hc]
    simp only [← Category.assoc]
    rw [← MonObj.mul_comp, lift_onQuotientHom, lift_onQuotientHom,
      lift_onQuotientHom, a.act_mul_right, MonObj.mul_comp]

@[simp]
theorem onQuotient_act_lift {T : Over S} (h : T ⟶ H.X) (g : T ⟶ G.X) :
    (onQuotient a q hk).act h (g ≫ q.hom.hom) = a.act h g ≫ q.hom.hom :=
  lift_onQuotientHom a q hk h g

/-- The quotient homomorphism intertwines the original and descended actions. -/
theorem onQuotient_isEquivariant : a.IsEquivariant (onQuotient a q hk) q :=
  fun h g => (onQuotient_act_lift a q hk h g).symm

/-- Equivariance uniquely determines the descended action morphism. -/
theorem onQuotient_hom_unique (b : AutomorphicAction H Q) (hb : a.IsEquivariant b q) :
    b.hom = (onQuotient a q hk).hom := by
  have := Dynamic.flagQuotient_effectiveEpi_whiskerLeft G q.hom.hom H.X
  apply Over.OverMorphism.ext
  apply (cancel_epi (H.X ◁ q.hom.hom).left).mp
  have he : (H.X ◁ q.hom.hom) ≫ b.hom = a.hom ≫ q.hom.hom := by
    have e := hb (fst H.X G.X) (snd H.X G.X)
    simpa only [act, ← lift_whiskerLeft_assoc, lift_fst_snd, Category.id_comp] using e.symm
  exact congrArg (fun f => f.left) (he.trans (fac_onQuotientHom a q hk).symm)

/-- Uniqueness as a bundled action. -/
theorem onQuotient_unique (b : AutomorphicAction H Q) (hb : a.IsEquivariant b q) :
    b = onQuotient a q hk :=
  ext_hom (onQuotient_hom_unique a q hk b hb)

omit hk in
/-- Kernel stability is exactly the condition for an action on the given fpqc
quotient compatible with its homomorphism. -/
theorem exists_onQuotient_iff :
    (∃ b : AutomorphicAction H Q, a.IsEquivariant b q) ↔
      a.IsStable (SubgroupFunctor.range (kernelι q)) := by
  constructor
  · rintro ⟨b, hb⟩
    exact isStable_kernel_of_equivariant a q b hb
  · intro hk
    exact ⟨onQuotient a q hk, onQuotient_isEquivariant a q hk⟩

end Langlands.GroupScheme.AutomorphicAction
