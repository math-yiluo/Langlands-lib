import Langlands.GroupScheme.Rational.InnerDiscrepancyOverlap
import Langlands.GroupScheme.LocalGroupIsoRefinement

/-! # Fpqc reflection of inner discrepancy -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LocalGroupIso

variable {S : Scheme.{u}} {G H A : GroupScheme S} {U V : Over S}
  {e : LocalGroupIso G H U} {a : AutomorphicAction A G}

/-- Inner discrepancy persists under every cover refinement. -/
theorem HasInnerDiscrepancy.refine (he : e.HasInnerDiscrepancy a) (r : V ⟶ U) :
    (e.refine r).HasInnerDiscrepancy a := by
  intro T b c
  obtain ⟨x, hx⟩ := he (b ≫ r) (c ≫ r)
  refine ⟨x, ?_⟩
  intro W t g
  simpa only [refine_toFun, Category.assoc] using hx t g

private abbrev fpqcProperty : MorphismProperty Scheme.{u} :=
  @QuasiCompact ⊓ (@Flat ⊓ @Surjective)

set_option backward.isDefEq.respectTransparency false in
private theorem fpqc_tensorHom {U' V' : Over S} (r : V ⟶ U) (s : V' ⟶ U')
    [QuasiCompact r.left] [Flat r.left] [Surjective r.left]
    [QuasiCompact s.left] [Flat s.left] [Surjective s.left] :
    fpqcProperty (r ⊗ₘ s).left :=
  MorphismProperty.pullbackMap (P := fpqcProperty)
    ⟨inferInstance, inferInstance, inferInstance⟩
    ⟨inferInstance, inferInstance, inferInstance⟩
    (Over.w r).symm (Over.w s).symm

/-- A faithful action lets an inner discrepancy descend from an fpqc refinement. -/
theorem HasInnerDiscrepancy.of_refine (r : V ⟶ U)
    [QuasiCompact r.left] [Flat r.left] [Surjective r.left]
    (ha : a.IsFaithful) (he : (e.refine r).HasInnerDiscrepancy a) :
    e.HasInnerDiscrepancy a := by
  obtain ⟨δ, hδ⟩ := he (fst V V) (snd V V)
  have hlocal {T : Over S} (t : T ⟶ V ⊗ V) :
      e.RepresentsDiscrepancy a ((t ≫ fst V V) ≫ r)
        ((t ≫ snd V V) ≫ r) (t ≫ δ) := by
    intro W s g
    simpa only [refine_toFun, Category.assoc] using hδ (s ≫ t) g
  have hrel {T : Over S} (b c : T ⟶ V ⊗ V)
      (hbc : b ≫ (r ⊗ₘ r) = c ≫ (r ⊗ₘ r)) : b ≫ δ = c ≫ δ := by
    have hb : (b ≫ fst V V) ≫ r = (c ≫ fst V V) ≫ r := by
      simpa only [Category.assoc, tensorHom_fst] using
        congrArg (fun t => t ≫ fst U U) hbc
    have hc : (b ≫ snd V V) ≫ r = (c ≫ snd V V) ≫ r := by
      simpa only [Category.assoc, tensorHom_snd] using
        congrArg (fun t => t ≫ snd U U) hbc
    have hbδ : e.RepresentsDiscrepancy a ((b ≫ fst V V) ≫ r)
        ((b ≫ snd V V) ≫ r) (b ≫ δ) := hlocal b
    rw [hb, hc] at hbδ
    exact RepresentsDiscrepancy.unique e a ha hbδ (hlocal c)
  let q := r ⊗ₘ r
  let : EffectiveEpi q.left := Cocycle.effectiveEpi_tensorHom r
  let d : (U ⊗ U).left ⟶ A.X.left :=
    EffectiveEpi.desc q.left δ.left (fun {T} b c hbc => by
      have hc : c ≫ (V ⊗ V).hom = b ≫ (V ⊗ V).hom := by
        rw [← Over.w q, ← Category.assoc, ← Category.assoc, hbc]
      let b₀ : Over.mk (b ≫ (V ⊗ V).hom) ⟶ V ⊗ V := Over.homMk b rfl
      let c₀ : Over.mk (b ≫ (V ⊗ V).hom) ⟶ V ⊗ V := Over.homMk c hc
      exact congrArg (fun t => t.left)
        (hrel b₀ c₀ (Over.OverMorphism.ext hbc)))
  have hd : q.left ≫ d = δ.left := EffectiveEpi.fac _ _ _
  let δ₀ : U ⊗ U ⟶ A.X := Over.homMk d (by
    apply (cancel_epi q.left).mp
    rw [← Category.assoc, hd, Over.w δ, Over.w q])
  have hδ₀ : q ≫ δ₀ = δ := Over.OverMorphism.ext hd
  have hq := fpqc_tensorHom r r
  let : QuasiCompact q.left := hq.1
  let : Flat q.left := hq.2.1
  let : Surjective q.left := hq.2.2
  let p := q ⊗ₘ (𝟙 G.X)
  have hid : fpqcProperty (𝟙 G.X : G.X ⟶ G.X).left := by
    change fpqcProperty (𝟙 G.X.left)
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  let : QuasiCompact (𝟙 G.X : G.X ⟶ G.X).left := hid.1
  let : Flat (𝟙 G.X : G.X ⟶ G.X).left := hid.2.1
  let : Surjective (𝟙 G.X : G.X ⟶ G.X).left := hid.2.2
  have hp := fpqc_tensorHom q (𝟙 G.X)
  let : QuasiCompact p.left := hp.1
  let : Flat p.left := hp.2.1
  let : Surjective p.left := hp.2.2
  apply e.hasInnerDiscrepancy_of_overlap a (δ := δ₀)
  apply Over.OverMorphism.ext
  apply (cancel_epi p.left).mp
  have h :
      p ≫ e.toFun (fst (U ⊗ U) G.X ≫ fst U U)
          (a.act (fst (U ⊗ U) G.X ≫ δ₀) (snd (U ⊗ U) G.X)) =
        p ≫ e.toFun (fst (U ⊗ U) G.X ≫ snd U U) (snd (U ⊗ U) G.X) := by
    rw [← e.naturality, ← e.naturality, a.naturality]
    simp only [p, ← Category.assoc, tensorHom_fst, tensorHom_snd, Category.comp_id]
    simp only [Category.assoc, hδ₀]
    simpa only [q, tensorHom_fst, tensorHom_snd, Category.assoc, refine_toFun] using
      hδ (fst (V ⊗ V) G.X) (snd (V ⊗ V) G.X)
  exact congrArg (fun t => t.left) h

/-- Innerness for a faithful action is invariant under fpqc cover refinement. -/
theorem hasInnerDiscrepancy_refine_iff (e : LocalGroupIso G H U)
    (a : AutomorphicAction A G) (ha : a.IsFaithful) (r : V ⟶ U)
    [QuasiCompact r.left] [Flat r.left] [Surjective r.left] :
    (e.refine r).HasInnerDiscrepancy a ↔ e.HasInnerDiscrepancy a :=
  ⟨fun h => h.of_refine r ha, fun h => h.refine r⟩

/-- The uniquely determined natural discrepancy cocycle commutes with refinement. -/
theorem innerCocycle_refine (e : LocalGroupIso G H U)
    (a : AutomorphicAction A G) (ha : a.IsFaithful)
    (he : e.HasInnerDiscrepancy a) (r : V ⟶ U) :
    (e.innerCocycle a ha he).refine r =
      (e.refine r).innerCocycle a ha (he.refine r) :=
  (e.refine r).innerCocycle_unique a ha (he.refine r)
    ((e.innerCocycle a ha he).refine r)
    (HasDiscrepancy.refine (e.innerCocycle_hasDiscrepancy a ha he) r)

/-- Construct the discrepancy cocycle before refinement from fpqc-local innerness. -/
def innerCocycleOfRefinement (e : LocalGroupIso G H U)
    (a : AutomorphicAction A G) (ha : a.IsFaithful) (r : V ⟶ U)
    [QuasiCompact r.left] [Flat r.left] [Surjective r.left]
    (he : (e.refine r).HasInnerDiscrepancy a) : Cocycle A U :=
  e.innerCocycle a ha (he.of_refine r ha)

/-- The descended cocycle represents the original local family's discrepancy. -/
theorem innerCocycleOfRefinement_hasDiscrepancy (e : LocalGroupIso G H U)
    (a : AutomorphicAction A G) (ha : a.IsFaithful) (r : V ⟶ U)
    [QuasiCompact r.left] [Flat r.left] [Surjective r.left]
    (he : (e.refine r).HasInnerDiscrepancy a) :
    e.HasDiscrepancy a (e.innerCocycleOfRefinement a ha r he) :=
  e.innerCocycle_hasDiscrepancy a ha (he.of_refine r ha)

/-- Refinement of the descended cocycle recovers the refined canonical cocycle. -/
theorem innerCocycleOfRefinement_refine (e : LocalGroupIso G H U)
    (a : AutomorphicAction A G) (ha : a.IsFaithful) (r : V ⟶ U)
    [QuasiCompact r.left] [Flat r.left] [Surjective r.left]
    (he : (e.refine r).HasInnerDiscrepancy a) :
    (e.innerCocycleOfRefinement a ha r he).refine r =
      (e.refine r).innerCocycle a ha he :=
  e.innerCocycle_refine a ha (he.of_refine r ha) r

end Langlands.GroupScheme.LocalGroupIso
