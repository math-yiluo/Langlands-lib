import Langlands.Sheaf.Equivariant.AnalyticGSheaves
import Langlands.Sheaf.Equivariant.LocalActionSmoothPart

/-!
# Admissible refinements on the twisted étale site

Let a topological group `G` act on an analytic space `X`. Étale `G`-sheaves are the
locally discrete sheaves on the twisted étale site for the lifts of the action to
distinguished étale objects. Their abelian structure and their derived compactly
supported cohomology use the admissible refinement condition
`HasAdmissibleRefinements` of this local action system. It follows from three
conditions on the plain étale site of `X`:

* every point of an étale object lies in the image of a morphism over `X` from a
  distinguished étale object;
* every distinguished étale object carries a lift of the action;
* for a morphism of distinguished étale objects over `X`, any two lifts are
  compatible with it on an open subgroup.

For a general local action system, the second half of `HasAdmissibleRefinements`
is equivalent to the covering of every object by objects with admissible local
actions.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.LocalActionSystem

open CategoryTheory

variable {T : Type*} [Category T] {G : Type*} [Group G] [TopologicalSpace G]
variable (L : LocalActionSystem T G) (J : GrothendieckTopology T)

/-- Every arrow factoring through an object with an admissible local action lies in
the refinement sieve of every cone over a cospan: the object itself is the common
refinement. -/
theorem admissibleSieve_le_fiberRefinementSieve {U V₁ V₂ W : T} (f₁ : V₁ ⟶ U)
    (f₂ : V₂ ⟶ U) (k₁ : W ⟶ V₁) (k₂ : W ⟶ V₂) (hk : k₁ ≫ f₁ = k₂ ≫ f₂) :
    L.admissibleSieve W ≤ L.fiberRefinementSieve f₁ f₂ k₁ k₂ := by
  rintro W' e ⟨V, k, f, H, a, ha, rfl⟩
  refine ⟨V, H, a, k, f ≫ k₁, f ≫ k₂, ha, ?_, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, hk]
  · rw [Category.assoc]
  · rw [Category.assoc]

/-- `HasAdmissibleRefinements` holds exactly when every arrow between objects with
admissible local actions restricts discreteness and objects with admissible local
actions cover every object. -/
theorem hasAdmissibleRefinements_iff :
    L.HasAdmissibleRefinements J ↔
      (∀ ⦃V V' : T⦄ ⦃H H' : OpenSubgroup G⦄ ⦃a : (H : Subgroup G) →* (End V)ᵐᵒᵖ⦄
        ⦃a' : (H' : Subgroup G) →* (End V')ᵐᵒᵖ⦄,
        L.IsAdmissible V H a → L.IsAdmissible V' H' a' → ∀ p : V' ⟶ V,
          IsRestrictionEquivariant a a' p) ∧ L.Covers J := by
  refine ⟨fun h => ⟨h.isRestrictionEquivariant, h.covers⟩, fun ⟨hres, hcov⟩ => ⟨hres, ?_⟩⟩
  intro U V₁ V₂ W f₁ f₂ k₁ k₂ hk
  exact J.superset_covering (L.admissibleSieve_le_fiberRefinementSieve f₁ f₂ k₁ k₂ hk) (hcov W)

end Langlands.Sheaf.Equivariant.LocalActionSystem

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory

universe u v z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- A distinguished étale morphism followed by an isomorphism of the target is
distinguished étale. -/
theorem IsDistinguishedEtale.comp_iso {X Y U : LocalizedCategory.{u, v, v} (K := K)}
    {f : U ⟶ X} (hf : IsDistinguishedEtale f) (e : X ≅ Y) :
    IsDistinguishedEtale (f ≫ e.hom) := by
  obtain ⟨het, Ubar, φ, hφ, hU, O, D, hO, hD, e', rfl⟩ := hf
  refine ⟨MorphismProperty.RespectsIso.postcomp _ e.hom _ het, Ubar, φ ≫ e.hom,
    MorphismProperty.RespectsIso.postcomp _ e.hom _ hφ, hU, O, D, hO, hD, e', ?_⟩
  exact (Category.assoc _ _ _).trans (congrArg (e'.hom ≫ ·) (Category.assoc _ _ _))

namespace ActionLift

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] [TopologicalSpace G]
variable {ρ : G →* Aut X} {U : LocalizedCategory.{u, v, v} (K := K)} {f : U ⟶ X}

/-- The conjugate `g H g⁻¹` of the subgroup of a lift. -/
def translateSubgroup (l : ActionLift ρ f) (g : G) : Subgroup G :=
  l.subgroup.comap (MulAut.conj g⁻¹).toMonoidHom

theorem mem_translateSubgroup (l : ActionLift ρ f) (g : G) (y : G) :
    y ∈ l.translateSubgroup g ↔ g⁻¹ * y * g ∈ l.subgroup := by
  change (MulAut.conj g⁻¹) y ∈ l.subgroup ↔ _
  rw [MulAut.conj_apply, inv_inv]

variable [IsTopologicalGroup G]

/-- Conjugation `y ↦ g⁻¹ y g` from `g H g⁻¹` to the subgroup `H` of a lift, as a
continuous homomorphism. -/
def translateHom (l : ActionLift ρ f) (g : G) : l.translateSubgroup g →ₜ* l.subgroup :=
  ⟨(MulAut.conj g⁻¹).toMonoidHom.subgroupComap l.subgroup,
    Continuous.subtype_mk
      ((continuous_const.mul continuous_subtype_val).mul continuous_const) _⟩

@[simp]
theorem coe_translateHom (l : ActionLift ρ f) (g : G) (y : l.translateSubgroup g) :
    ((l.translateHom g y : l.subgroup) : G) = g⁻¹ * y * g := by
  change (MulAut.conj g⁻¹) (y : G) = _
  rw [MulAut.conj_apply, inv_inv]

/-- The translate of a lift by `g`: a lift to `f ≫ ρ g` of the action, by the
conjugate subgroup `g H g⁻¹`, where `y` acts as `g⁻¹ y g` acts for the given lift.
It is the lift to the translate `gU` of the object. -/
def translate (l : ActionLift ρ f) (g : G) : ActionLift ρ (f ≫ (ρ g).hom) where
  subgroup := l.translateSubgroup g
  isOpen_subgroup := l.isOpen_subgroup.preimage
    ((continuous_const.mul continuous_id).mul continuous_const)
  action := l.action.comp (l.translateHom g).toMonoidHom
  isContinuousAction := l.isContinuousAction.comp (l.translateHom g)
  equivariant y := by
    change (l.action (l.translateHom g y)).hom ≫ f ≫ (ρ g).hom = _
    rw [← Category.assoc, l.equivariant, Category.assoc, Category.assoc,
      ← Langlands.Sheaf.Equivariant.TwistedOver.rho_mul_hom,
      ← Langlands.Sheaf.Equivariant.TwistedOver.rho_mul_hom, coe_translateHom]
    simp only [mul_assoc, mul_inv_cancel_left]

theorem translate_action (l : ActionLift ρ f) (g : G) (y : (l.translate g).subgroup) :
    (l.translate g).action y = l.action (l.translateHom g y) :=
  rfl

end ActionLift

end Langlands.Analytic.SaturatedAtlasPresentation

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver

universe u v z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Conditions

variable (X : LocalizedCategory.{u, v, v} (K := K))

/-- Distinguished étale neighbourhoods: every point of an étale object over `X` lies
in the image of a morphism over `X` from a distinguished étale object. -/
def HasDistinguishedEtaleNeighbourhoods : Prop :=
  ∀ (U : EtaleSite X) (x : (EtaleSite.points X).obj U), ∃ (V : EtaleSite X) (f : V ⟶ U),
    IsDistinguishedEtale V.hom ∧ x ∈ Set.range ((EtaleSite.points X).map f)

variable {X} {G : Type z} [Group G] [TopologicalSpace G] (ρ : G →* Aut X)

/-- Every distinguished étale object carries a lift of the action. -/
def HasDistinguishedEtaleLifts : Prop :=
  ∀ ⦃V : EtaleSite X⦄, IsDistinguishedEtale V.hom → Nonempty (ActionLift ρ V.hom)

/-- Lifts on distinguished étale objects are compatible with morphisms over `X`: for
`f : V ⟶ U` and lifts `a` on `U` and `b` on `V`, the arrow `f` intertwines the two
actions on an open subgroup. -/
def HasCompatibleDistinguishedEtaleLifts : Prop :=
  ∀ ⦃U V : EtaleSite X⦄ (f : V ⟶ U), IsDistinguishedEtale U.hom → IsDistinguishedEtale V.hom →
    ∀ (a : ActionLift ρ U.hom) (b : ActionLift ρ V.hom),
      ∃ N : Subgroup G, IsOpen (N : Set G) ∧ ∃ (ha : N ≤ a.subgroup) (hb : N ≤ b.subgroup),
        ∀ (g : G) (hg : g ∈ N),
          (b.action ⟨g, hb hg⟩).hom ≫ f.left = f.left ≫ (a.action ⟨g, ha hg⟩).hom

end Conditions

section Refinements

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G]
variable [TopologicalSpace G] (ρ : G →* Aut X)

/-- Distinguished étale neighbourhoods carrying lifts cover every object of the
twisted étale site. -/
theorem covers_distinguishedLiftSystem (hA : HasDistinguishedEtaleNeighbourhoods X)
    (hB : HasDistinguishedEtaleLifts ρ) :
    (distinguishedLiftSystem ρ).Covers (twistedEtaleTopology ρ) := by
  intro U
  change Sieve.functorPullback (ι etale ρ) _ ∈ etaleTopology X U.obj
  refine mem_etaleTopology_of_jointlySurjective _ fun x => ?_
  obtain ⟨V, f, hV, hx⟩ := hA U.obj x
  let l : ActionLift ρ V.hom := (hB hV).some
  refine ⟨V, f, ?_, hx⟩
  refine ⟨(ι etale ρ).obj V, 𝟙 _, (ι etale ρ).map f, liftOpenSubgroup l,
    liftAction (U := (ι etale ρ).obj V) l, ⟨hV, l, le_rfl, ?_⟩, Category.id_comp _⟩
  exact MonoidHom.ext fun _ => rfl

/-- Every arrow between distinguished étale objects with lifts restricts
discreteness. A twisted arrow `p : V' ⟶ V` with twist `g` is an arrow over `X`
from the translate `gV'`, which is distinguished étale and carries the translate
of the lift on `V'`; compatibility of the two lifts along it on an open subgroup
`N` gives, for `h` in `g⁻¹ N g`, the identity
`a' h ≫ p = p ≫ a (g h g⁻¹)`. -/
theorem isRestrictionEquivariant_distinguishedLiftSystem [IsTopologicalGroup G]
    (hC : HasCompatibleDistinguishedEtaleLifts ρ) {V V' : TwistedOver (etale (K := K)) ρ}
    {H H' : OpenSubgroup G} {a : (H : Subgroup G) →* (End V)ᵐᵒᵖ}
    {a' : (H' : Subgroup G) →* (End V')ᵐᵒᵖ}
    (ha : (distinguishedLiftSystem ρ).IsAdmissible V H a)
    (ha' : (distinguishedLiftSystem ρ).IsAdmissible V' H' a') (p : V' ⟶ V) :
    IsRestrictionEquivariant a a' p := by
  obtain ⟨hV, l, hH, rfl⟩ := ha
  obtain ⟨hV', l', hH', rfl⟩ := ha'
  set g := Hom.twist p with hg
  have hV'' : IsDistinguishedEtale ((translate etale ρ g).obj V'.obj).hom :=
    hV'.comp_iso (ρ g)
  obtain ⟨N, hN, hNl, hNl', hNp⟩ :=
    hC (untwist g p hg.symm) hV hV'' l (l'.translate g)
  intro K' hK'
  let N' : OpenSubgroup G := ⟨N, hN⟩ ⊓ K'
  let M' : OpenSubgroup G := ⟨(N' : Subgroup G).comap (MulAut.conj g).toMonoidHom,
    N'.isOpen.preimage ((continuous_const.mul continuous_id).mul continuous_const)⟩
  refine ⟨H' ⊓ M', inf_le_left, fun h hh => ?_⟩
  have hhM : g * h * g⁻¹ ∈ N' := by
    have := (OpenSubgroup.mem_inf.1 hh).2
    change (MulAut.conj g) (h : G) ∈ N' at this
    rwa [MulAut.conj_apply] at this
  have hkN : g * h * g⁻¹ ∈ N := (OpenSubgroup.mem_inf.1 hhM).1
  have hkK : g * h * g⁻¹ ∈ K' := (OpenSubgroup.mem_inf.1 hhM).2
  refine ⟨⟨g * h * g⁻¹, hK' hkK⟩, hkK, ?_⟩
  refine hom_ext ?_ ?_
  · simp only [comp_twist]
    change g * (h : G)⁻¹ = (g * h * g⁻¹)⁻¹ * g
    group
  · simp only [comp_left]
    have hx : (g * h * g⁻¹)⁻¹ ∈ N := inv_mem hkN
    have key := hNp _ hx
    change (l'.action (l'.translateHom g ⟨_, hNl' hx⟩)).hom ≫ Hom.left p =
      Hom.left p ≫ (l.action ⟨_, hNl hx⟩).hom at key
    change (l'.action (Subgroup.inclusion hH' h)⁻¹).hom ≫ Hom.left p =
      Hom.left p ≫ (l.action (Subgroup.inclusion hH ⟨g * h * g⁻¹, hK' hkK⟩)⁻¹).hom
    have e₁ : (Subgroup.inclusion hH' h)⁻¹ =
        l'.translateHom g ⟨(g * h * g⁻¹)⁻¹, hNl' hx⟩ := by
      apply Subtype.ext
      simp only [ActionLift.coe_translateHom, InvMemClass.coe_inv, Subgroup.coe_inclusion]
      group
    have e₂ : (Subgroup.inclusion hH ⟨g * h * g⁻¹, hK' hkK⟩)⁻¹ =
        (⟨(g * h * g⁻¹)⁻¹, hNl hx⟩ : l.subgroup) := by
      apply Subtype.ext
      simp only [InvMemClass.coe_inv, Subgroup.coe_inclusion]
    rw [e₁, e₂]
    exact key

/-- The three conditions give admissible refinements for the lifts on distinguished
étale objects, and hence the abelian structure of étale `G`-sheaves of modules and
their compactly supported cohomology. -/
theorem hasAdmissibleRefinements_distinguishedLiftSystem [IsTopologicalGroup G]
    (hA : HasDistinguishedEtaleNeighbourhoods X) (hB : HasDistinguishedEtaleLifts ρ)
    (hC : HasCompatibleDistinguishedEtaleLifts ρ) :
    (distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ) :=
  (LocalActionSystem.hasAdmissibleRefinements_iff _ _).2
    ⟨fun _ _ _ _ _ _ ha ha' p => isRestrictionEquivariant_distinguishedLiftSystem ρ hC ha ha' p,
      covers_distinguishedLiftSystem ρ hA hB⟩

end Refinements

end Langlands.Sheaf.Equivariant.Analytic
