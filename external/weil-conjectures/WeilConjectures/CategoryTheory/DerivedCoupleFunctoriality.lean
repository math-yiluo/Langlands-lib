/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ExactCoupleConvergence

/-!
# Functoriality of derived exact couples

Source: Stacks Project, Homological Algebra, Definitions 12.21.1 and 12.21.3,
Lemmas 12.21.2 and 12.21.4 (Tags 011Q, 011R, 011S, 011T)
(blueprint: lem-sp-derived-couple-functoriality).
-/

@[expose] public section

universe u v

open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheory.BigradedExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A degree-preserving morphism of type-`s` bigraded exact couples.
Source: Stacks Project, Homological Algebra, Definition 12.21.1, Tag 011Q
(blueprint: lem-sp-derived-couple-functoriality). -/
structure CoupleMorphism {s : ℕ} (X Y : BigradedExactCouple C s) where
  tD : ∀ p q : ℤ, X.D p q ⟶ Y.D p q
  tE : ∀ p q : ℤ, X.E p q ⟶ Y.E p q
  alpha_comm : ∀ p q : ℤ,
    tD p q ≫ Y.alpha p q = X.alpha p q ≫ tD (p - 1) (q + 1)
  f_comm : ∀ p q : ℤ,
    tE p q ≫ Y.f p q = X.f p q ≫ tD (p + 2) (q - 1)
  g_comm : ∀ p q : ℤ,
    tD p q ≫ Y.g p q = X.g p q ≫ tE (p + s) (q - s)

private theorem transport_square {C : Type u} [Category.{v} C]
    {F G : ℤ → ℤ → C} (t : ∀ p q, F p q ⟶ G p q)
    {p q p' q' : ℤ} (hp : p = p') (hq : q = q') :
    eqToHom (congrArg₂ F hp hq) ≫ t p' q' =
      t p q ≫ eqToHom (congrArg₂ G hp hq) := by
  subst p'
  subst q'
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Restriction to the alpha image and passage to differential homology preserve
all three exact-couple squares for one derivation.

Proof. Write d = f ≫ g. The f and g squares give tE ≫ dY = dX ≫ tE at the
outgoing bidegree. Use the kernel universal property to restrict tE to cycles.
At the incoming bidegree the same equation makes the induced cycle map carry the
lifted incoming differential to the target's lifted incoming differential. Compose
with the target cokernel projection; this kills the source boundary map and so
uniquely descends to the source cokernel. The alpha square induces the map on its
image, with the prescribed equation for derivedDInclusion. For the derived alpha
square, postcompose with the target image inclusion and use the original alpha
square and the DerivedMaps.alpha_comm equations. For the derived f square, first
precompose with the source derivedEProjection, then postcompose with the target
image inclusion: the two DerivedMaps.f_comm equations reduce it to the original
f square and the kernel-map equation. For the derived g square, precompose with
the source factorThruImage(alpha): the two DerivedMaps.g_comm equations reduce it
to the original g square, the cycle-map equation, and the quotient-map equation.
These inclusions are monic and projections epimorphic, so cancellation proves
all three squares. The chosen DerivedMaps in derived are characterized by their
restriction equations, so the argument applies to the actual derived couples.
Source: Stacks Project, Definition 12.21.1 and Lemma 12.21.2, Tags 011Q, 011R
(blueprint: lem-sp-derived-couple-functoriality). -/
private theorem derivedCoupleMorphismStep {C : Type u} [Category.{v} C] [Abelian C]
    {s : ℕ} (X Y : BigradedExactCouple C s)
    (tD : ∀ p q : ℤ, X.D p q ⟶ Y.D p q)
    (tE : ∀ p q : ℤ, X.E p q ⟶ Y.E p q)
    (ha : ∀ p q, tD p q ≫ Y.alpha p q = X.alpha p q ≫ tD (p - 1) (q + 1))
    (hf : ∀ p q, tE p q ≫ Y.f p q = X.f p q ≫ tD (p + 2) (q - 1))
    (hg : ∀ p q, tD p q ≫ Y.g p q = X.g p q ≫ tE (p + s) (q - s)) :
    ∃ (a : ∀ p q : ℤ, X.derivedD p q ⟶ Y.derivedD p q)
      (b : ∀ p q : ℤ, X.derivedE p q ⟶ Y.derivedE p q),
      (∀ p q, a p q ≫ Y.derived.alpha p q =
        X.derived.alpha p q ≫ a (p - 1) (q + 1)) ∧
      (∀ p q, b p q ≫ Y.derived.f p q =
        X.derived.f p q ≫ a (p + 2) (q - 1)) ∧
      (∀ p q, a p q ≫ Y.derived.g p q =
        X.derived.g p q ≫ b (p + (s + 1 : ℕ)) (q - (s + 1 : ℕ))) ∧
      (∀ p q, a p q ≫ Y.derivedDInclusion p q =
        X.derivedDInclusion p q ≫ tD p q) ∧
      (∀ p q, ∃ k : kernel (X.d p q) ⟶ kernel (Y.d p q),
        k ≫ kernel.ι (Y.d p q) = kernel.ι (X.d p q) ≫ tE p q ∧
        X.derivedEProjection p q ≫ b p q = k ≫ Y.derivedEProjection p q) := by
  classical
  have hd : ∀ p q, tE p q ≫ Y.d p q =
      X.d p q ≫ tE (p + 2 + s) (q - 1 - s) := by
    intro p q
    dsimp [d]
    rw [← Category.assoc, hf, Category.assoc, hg, Category.assoc]
  have hin : ∀ p q, X.dInto p q ≫ tE p q =
      tE (p - s - 2) (q + s + 1) ≫ Y.dInto p q := by
    intro p q
    dsimp [dInto]
    have hp : p - (s : ℤ) - 2 + 2 + s = p := by omega
    have hq : q + (s : ℤ) + 1 - 1 - s = q := by omega
    rw [Category.assoc, transport_square tE hp hq, ← Category.assoc, ← hd,
      Category.assoc]
  let k := fun p q ↦ kernel.map (X.d p q) (Y.d p q) (tE p q)
    (tE (p + 2 + s) (q - 1 - s)) (hd p q).symm
  have hk : ∀ p q, k p q ≫ kernel.ι (Y.d p q) =
      kernel.ι (X.d p q) ≫ tE p q := by
    intro p q
    exact kernel.lift_ι _ _ _
  let dx := fun p q ↦ kernel.lift (X.d p q) (X.dInto p q) (X.dInto_comp_d p q)
  let dy := fun p q ↦ kernel.lift (Y.d p q) (Y.dInto p q) (Y.dInto_comp_d p q)
  have hboundary : ∀ p q, dx p q ≫ k p q =
      tE (p - s - 2) (q + s + 1) ≫ dy p q := by
    intro p q
    apply (cancel_mono (kernel.ι (Y.d p q))).mp
    simp only [Category.assoc, hk, dx, dy, kernel.lift_ι, kernel.lift_ι_assoc, hin]
  let b := fun p q ↦ cokernel.desc (dx p q) (k p q ≫ Y.derivedEProjection p q)
    (by rw [← Category.assoc, hboundary, Category.assoc];
        exact (Category.assoc _ _ _).symm.trans (by simp [dy, derivedEProjection]))
  have hb : ∀ p q, X.derivedEProjection p q ≫ b p q =
      k p q ≫ Y.derivedEProjection p q := by
    intro p q
    exact cokernel.π_desc _ _ _
  let a := fun p q ↦ image.map (Arrow.homMk' (tD (p + 1) (q - 1))
    (tD ((p + 1) - 1) ((q - 1) + 1)) (ha (p + 1) (q - 1)))
  have hi : ∀ p q, a p q ≫ Y.derivedDInclusion p q =
      X.derivedDInclusion p q ≫ tD p q := by
    intro p q
    dsimp only [a, derivedDInclusion, derivedD]
    rw [← Category.assoc]
    rw [image.map_homMk'_ι]
    simp only [Category.assoc]
    rw [transport_square tD (by omega) (by omega)]
  refine ⟨a, b, ?_, ?_, ?_, hi, fun p q ↦ ⟨k p q, hk p q, hb p q⟩⟩
  · intro p q
    have hx := (Classical.choice X.derivedMaps_exists).alpha_comm p q
    have hy := (Classical.choice Y.derivedMaps_exists).alpha_comm p q
    change X.derived.alpha p q ≫ X.derivedDInclusion (p - 1) (q + 1) =
      X.derivedDInclusion p q ≫ X.alpha p q at hx
    change Y.derived.alpha p q ≫ Y.derivedDInclusion (p - 1) (q + 1) =
      Y.derivedDInclusion p q ≫ Y.alpha p q at hy
    have : Mono (Y.derivedDInclusion (p - 1) (q + 1)) := by
      dsimp [derivedDInclusion]
      infer_instance
    apply (cancel_mono (Y.derivedDInclusion (p - 1) (q + 1))).mp
    simp only [Category.assoc]
    rw [hy, ← Category.assoc, hi, Category.assoc, ha, hi]
    simpa only [Category.assoc] using
      (congrArg (fun z ↦ z ≫ tD (p - 1) (q + 1)) hx).symm
  · intro p q
    have hx := (Classical.choice X.derivedMaps_exists).f_comm p q
    have hy := (Classical.choice Y.derivedMaps_exists).f_comm p q
    change X.derivedEProjection p q ≫ X.derived.f p q ≫
      X.derivedDInclusion (p + 2) (q - 1) = kernel.ι (X.d p q) ≫ X.f p q at hx
    change Y.derivedEProjection p q ≫ Y.derived.f p q ≫
      Y.derivedDInclusion (p + 2) (q - 1) = kernel.ι (Y.d p q) ≫ Y.f p q at hy
    have : Mono (Y.derivedDInclusion (p + 2) (q - 1)) := by
      dsimp [derivedDInclusion]
      infer_instance
    have : Epi (X.derivedEProjection p q) := by
      dsimp [derivedEProjection]
      infer_instance
    apply (cancel_epi (X.derivedEProjection p q)).mp
    apply (cancel_mono (Y.derivedDInclusion (p + 2) (q - 1))).mp
    simp only [Category.assoc]
    rw [← Category.assoc (X.derivedEProjection p q) (b p q), hb,
      Category.assoc, hy, ← Category.assoc, hk, Category.assoc, hf,
      hi]
    simpa only [Category.assoc] using
      (congrArg (fun z ↦ z ≫ tD (p + 2) (q - 1)) hx).symm
  · intro p q
    have hx := (Classical.choice X.derivedMaps_exists).g_comm p q
    have hy := (Classical.choice Y.derivedMaps_exists).g_comm p q
    change factorThruImage (X.alpha (p + 1) (q - 1)) ≫ X.derived.g p q =
      X.gToCycles (p + 1) (q - 1) ≫
        X.derivedEProjection ((p + 1) + s) ((q - 1) - s) ≫ eqToHom _ at hx
    change factorThruImage (Y.alpha (p + 1) (q - 1)) ≫ Y.derived.g p q =
      Y.gToCycles (p + 1) (q - 1) ≫
        Y.derivedEProjection ((p + 1) + s) ((q - 1) - s) ≫ eqToHom _ at hy
    have hc : tD (p + 1) (q - 1) ≫ Y.gToCycles (p + 1) (q - 1) =
        X.gToCycles (p + 1) (q - 1) ≫ k ((p + 1) + s) ((q - 1) - s) := by
      apply (cancel_mono (kernel.ι (Y.d ((p + 1) + s) ((q - 1) - s)))).mp
      dsimp only [gToCycles]
      simp only [Category.assoc, kernel.lift_ι, hk]
      rw [← Category.assoc, kernel.lift_ι, hg]
    have hfactor : factorThruImage (X.alpha (p + 1) (q - 1)) ≫ a p q =
        tD (p + 1) (q - 1) ≫ factorThruImage (Y.alpha (p + 1) (q - 1)) :=
      image.factor_map (Arrow.homMk' _ _ (ha (p + 1) (q - 1)))
    have ht := transport_square b
      (show (p + 1) + (s : ℤ) = p + (s + 1 : ℕ) by omega)
      (show (q - 1) - (s : ℤ) = q - (s + 1 : ℕ) by omega)
    apply (cancel_epi (factorThruImage (X.alpha (p + 1) (q - 1)))).mp
    rw [← Category.assoc, hfactor, Category.assoc, hy,
      ← Category.assoc (factorThruImage (X.alpha (p + 1) (q - 1)))
        (X.derived.g p q), hx]
    simp only [Category.assoc]
    rw [ht, ← Category.assoc (X.derivedEProjection ((p + 1) + s) ((q - 1) - s)), hb]
    simp only [← Category.assoc]
    rw [hc]


set_option backward.isDefEq.respectTransparency false in
private theorem extendedPullback_transport {C : Type u} [Category.{v} C] [Abelian C]
    {A B P Q : C} (U : Subobject A) (V : Subobject B)
    (px : (U : C) ⟶ P) (py : (V : C) ⟶ Q)
    (t : A ⟶ B) (z : (U : C) ⟶ (V : C)) (e : P ⟶ Q)
    (hz : z ≫ V.arrow = U.arrow ≫ t) (hp : z ≫ py = px ≫ e)
    (S : Subobject P) (R : Subobject Q)
    (h : R.Factors (S.arrow ≫ e)) :
    ((Subobject.«exists» V.arrow).obj ((Subobject.pullback py).obj R)).Factors
      (((Subobject.«exists» U.arrow).obj ((Subobject.pullback px).obj S)).arrow ≫ t) := by
  classical
  let SX := (Subobject.pullback px).obj S
  let SY := (Subobject.pullback py).obj R
  let UX := (Subobject.«exists» U.arrow).obj SX
  let VY := (Subobject.«exists» V.arrow).obj SY
  have heq : UX = Subobject.mk (SX.arrow ≫ U.arrow) := by
    dsimp [UX]
    rw [Subobject.exists_iso_map, ← Subobject.map_mk, Subobject.mk_arrow]
  let ux := (Subobject.isoOfEqMk UX (SX.arrow ≫ U.arrow) heq).hom
  have hux : ux ≫ SX.arrow ≫ U.arrow = UX.arrow := by
    simpa only [ux, Subobject.isoOfEqMk_hom, Category.assoc] using
      (Subobject.ofLEMk_comp heq.le)
  have hf : R.Factors (SX.arrow ≫ z ≫ py) := by
    rw [hp]
    have hs : S.Factors (SX.arrow ≫ px) :=
      (pullback_factors_iff px S SX.arrow).mp (Subobject.factors_self SX)
    have hh := Subobject.factors_of_factors_right (S.factorThru _ hs) h
    simpa only [← Category.assoc, Subobject.factorThru_arrow] using hh
  have hsy : SY.Factors (SX.arrow ≫ z) :=
    pullback_factors py R _ (by simpa only [Category.assoc] using hf)
  let sy := SY.factorThru _ hsy
  let vy : (SY : C) ⟶ (VY : C) := (Subobject.imageFactorisation V.arrow SY).F.e
  have hvy : vy ≫ VY.arrow = SY.arrow ≫ V.arrow :=
    (Subobject.imageFactorisation V.arrow SY).F.fac
  apply (Subobject.factors_iff _ _).mpr
  refine ⟨ux ≫ sy ≫ vy, ?_⟩
  change (ux ≫ sy ≫ vy) ≫ VY.arrow = UX.arrow ≫ t
  rw [Category.assoc, Category.assoc, hvy,
    ← Category.assoc sy, Subobject.factorThru_arrow, Category.assoc,
    hz]
  simpa only [Category.assoc] using congrArg (fun a ↦ a ≫ t) hux

/-- A compatible family of differential maps preserves the finite cycle and boundary
subobjects in the initial page. No limiting subobjects are assumed.

Proof. Induct on r, simultaneously proving preservation of Z_r and B_r and the
commutation of the restricted initial map with the tower projection to page r.
For r = 0, Z_0 is the whole page, B_0 is zero, and the projection is its inclusion;
projection commutation is the given equality e_0 = t. At the successor, differential
commutation sends the kernel of d_r into the target kernel and its incoming image
into the target incoming image (rewrite the incoming bidegrees in dInto). The
projection square from the induction hypothesis therefore maps their pullbacks
into the target pullbacks. Postcomposing these maps with the Z_r inclusions and
using Z_succ and B_succ proves preservation of the next cycles and boundaries.
The kernel inclusion cancels to identify the new cycleLift map with the old
cycleLift followed by the given kernel map. Compose that equation with the target
derivedEProjection and use the kernel/projection compatibility and projection_succ
to prove the successor projection square. This completes the simultaneous induction.
Source: Stacks Project, Definition 12.21.3 and Lemma 12.21.2, Tags 011S, 011R,
and blueprint def-sp-convergence
(blueprint: lem-sp-derived-couple-functoriality). -/
private theorem exactCoupleFiniteTransport {C : Type u} [Category.{v} C] [Abelian C]
    (X Y : BigradedExactCouple C 0)
    (t : ∀ p q : ℤ, X.E p q ⟶ Y.E p q)
    (e : ∀ (r : ℕ) (p q : ℤ), (X.pageCouple r).E p q ⟶ (Y.pageCouple r).E p q)
    (hzero : ∀ p q, e 0 p q = t p q)
    (hd : ∀ r p q, e r p q ≫ (Y.pageCouple r).d p q =
      (X.pageCouple r).d p q ≫ e r (p + 2 + r) (q - 1 - r))
    (hnext : ∀ r p q,
      ∃ k : kernel ((X.pageCouple r).d p q) ⟶ kernel ((Y.pageCouple r).d p q),
        k ≫ kernel.ι ((Y.pageCouple r).d p q) =
          kernel.ι ((X.pageCouple r).d p q) ≫ e r p q ∧
        (X.pageCouple r).derivedEProjection p q ≫ e (r + 1) p q =
          k ≫ (Y.pageCouple r).derivedEProjection p q) :
    ∀ r p q,
      (Y.cycleBoundaryTower.Z r p q).Factors
        ((X.cycleBoundaryTower.Z r p q).arrow ≫ t p q) ∧
      (Y.cycleBoundaryTower.B r p q).Factors
        ((X.cycleBoundaryTower.B r p q).arrow ≫ t p q) := by
  classical
  let TX := X.cycleBoundaryTower
  let TY := Y.cycleBoundaryTower
  have hind : ∀ r p q, ∃ z : (TX.Z r p q : C) ⟶ (TY.Z r p q : C),
      z ≫ (TY.Z r p q).arrow = (TX.Z r p q).arrow ≫ t p q ∧
      z ≫ TY.projection r p q = TX.projection r p q ≫ e r p q := by
    intro r
    induction r with
    | zero =>
      intro p q
      have hz : (TY.Z 0 p q).Factors ((TX.Z 0 p q).arrow ≫ t p q) := by
        rw [TY.Z_zero]
        exact Subobject.top_factors _
      refine ⟨(TY.Z 0 p q).factorThru _ hz, Subobject.factorThru_arrow _ _ _, ?_⟩
      rw [TX.projection_zero, TY.projection_zero, hzero]
      exact Subobject.factorThru_arrow _ _ _
    | succ r ih =>
      intro p q
      obtain ⟨z, hz, hp⟩ := ih p q
      have hkern : (kernelSubobject ((Y.pageCouple r).d p q)).Factors
          ((kernelSubobject ((X.pageCouple r).d p q)).arrow ≫ e r p q) := by
        apply kernelSubobject_factors
        rw [Category.assoc, hd, ← Category.assoc, kernelSubobject_arrow_comp, zero_comp]
      have hZ := extendedPullback_transport (TX.Z r p q) (TY.Z r p q)
        (TX.projection r p q) (TY.projection r p q) (t p q) z (e r p q) hz hp
        (kernelSubobject ((X.pageCouple r).d p q))
        (kernelSubobject ((Y.pageCouple r).d p q)) hkern
      rw [← TX.Z_succ, ← TY.Z_succ] at hZ
      let zn := (TY.Z (r + 1) p q).factorThru _ hZ
      have hzn : zn ≫ (TY.Z (r + 1) p q).arrow =
          (TX.Z (r + 1) p q).arrow ≫ t p q := Subobject.factorThru_arrow _ _ _
      refine ⟨zn, hzn, ?_⟩
      obtain ⟨k, hk, hkn⟩ := hnext r p q
      have hc : TX.cycleLift r p q ≫ k = zn ≫ TY.cycleLift r p q := by
        apply (cancel_mono (kernel.ι ((Y.pageCouple r).d p q))).mp
        rw [Category.assoc, hk, ← Category.assoc, TX.cycleLift_comm,
          Category.assoc, ← hp, ← Category.assoc,
          Category.assoc zn, TY.cycleLift_comm, ← Category.assoc]
        congr 1
        apply (cancel_mono (TY.Z r p q).arrow).mp
        rw [Category.assoc, hz, ← Category.assoc, Subobject.ofLE_arrow,
          Category.assoc, Subobject.ofLE_arrow, hzn]
      rw [TX.projection_succ, TY.projection_succ, ← Category.assoc, ← hc,
        Category.assoc, ← hkn, Category.assoc]
  intro r p q
  obtain ⟨z, hz, hp⟩ := hind r p q
  refine ⟨?_, ?_⟩
  · rw [← hz]
    exact Subobject.factors_comp_arrow z
  · cases r with
    | zero =>
      have hx : (TX.B 0 p q).arrow = 0 := by
        apply (Subobject.bot_factors_iff_zero _).mp
        rw [← TX.B_zero]
        exact Subobject.factors_self _
      rw [hx, zero_comp]
      exact Subobject.factors_zero
    | succ r =>
      obtain ⟨z, hz, hp⟩ := hind r p q
      have hin : (X.pageCouple r).dInto p q ≫ e r p q =
          e r (p - r - 2) (q + r + 1) ≫ (Y.pageCouple r).dInto p q := by
        dsimp only [dInto]
        rw [Category.assoc, transport_square (e r) (by omega) (by omega),
          ← Category.assoc, ← hd, Category.assoc]
      have him : (imageSubobject ((Y.pageCouple r).dInto p q)).Factors
          ((imageSubobject ((X.pageCouple r).dInto p q)).arrow ≫ e r p q) := by
        apply (Subobject.factors_iff _ _).mpr
        refine ⟨imageSubobjectMap (Arrow.homMk' _ _ hin.symm), ?_⟩
        exact imageSubobjectMap_arrow _
      have hB := extendedPullback_transport (TX.Z r p q) (TY.Z r p q)
        (TX.projection r p q) (TY.projection r p q) (t p q) z (e r p q) hz hp
        (imageSubobject ((X.pageCouple r).dInto p q))
        (imageSubobject ((Y.pageCouple r).dInto p q)) him
      rw [← TX.B_succ, ← TY.B_succ] at hB
      exact hB


private noncomputable def nextMorphism {s : ℕ} {X Y : BigradedExactCouple C s}
    (T : CoupleMorphism X Y) : CoupleMorphism X.derived Y.derived :=
  let h := derivedCoupleMorphismStep X Y T.tD T.tE T.alpha_comm T.f_comm T.g_comm
  { tD := h.choose
    tE := h.choose_spec.choose
    alpha_comm := h.choose_spec.choose_spec.1
    f_comm := h.choose_spec.choose_spec.2.1
    g_comm := h.choose_spec.choose_spec.2.2.1 }

private theorem nextMorphism_inclusion {s : ℕ} {X Y : BigradedExactCouple C s}
    (T : CoupleMorphism X Y) (p q : ℤ) :
    (nextMorphism T).tD p q ≫ Y.derivedDInclusion p q =
      X.derivedDInclusion p q ≫ T.tD p q :=
  (derivedCoupleMorphismStep X Y T.tD T.tE T.alpha_comm T.f_comm T.g_comm)
    |>.choose_spec.choose_spec.2.2.2.1 p q

private theorem nextMorphism_projection {s : ℕ} {X Y : BigradedExactCouple C s}
    (T : CoupleMorphism X Y) (p q : ℤ) :
    ∃ k : kernel (X.d p q) ⟶ kernel (Y.d p q),
      k ≫ kernel.ι (Y.d p q) = kernel.ι (X.d p q) ≫ T.tE p q ∧
      X.derivedEProjection p q ≫ (nextMorphism T).tE p q =
        k ≫ Y.derivedEProjection p q :=
  (derivedCoupleMorphismStep X Y T.tD T.tE T.alpha_comm T.f_comm T.g_comm)
    |>.choose_spec.choose_spec.2.2.2.2 p q

private theorem morphism_d {s : ℕ} {X Y : BigradedExactCouple C s}
    (T : CoupleMorphism X Y) (p q : ℤ) :
    T.tE p q ≫ Y.d p q = X.d p q ≫ T.tE (p + 2 + s) (q - 1 - s) := by
  dsimp [d]
  rw [← Category.assoc, T.f_comm, Category.assoc, T.g_comm, Category.assoc]

private theorem factors_iff_image_le {A B : C} (P : Subobject B) (f : A ⟶ B) :
    P.Factors f ↔ imageSubobject f ≤ P := by
  constructor
  · intro h
    exact imageSubobject_le f (P.factorThru f h) (P.factorThru_arrow f h)
  · intro h
    apply (Subobject.factors_iff _ _).mpr
    exact ⟨factorThruImageSubobject f ≫ Subobject.ofLE _ _ h, by simp⟩

/-- A morphism of exact couples induces compatible morphisms on every derived page,
and on the limiting page. The latter carries limiting cycles and boundaries into those
of the target and hence descends to the quotient at infinity, when the limits exist.

Proof, Step 1 (def-sp-exact-couple, lem-sp-derived-couple-exact): the three squares
imply differential commutation. Restrict tE to differential kernels and descend through
boundaries to obtain the derived E map. Restrict tD to the incoming alpha image to obtain
the derived D map. The restriction and quotient equations uniquely characterize these
maps. The three structure-map squares descend, since alpha, f and g in the derived
couple are defined by these same restrictions, factorizations and quotient projections.
Step 2 (lem-sp-derived-couple-exact): each derived couple is again exact. Induct on n
to obtain morphisms M n of the type-n couples, beginning with T. The successor D map
commutes with derivedDInclusion and the successor E map with derivedEProjection through
the induced kernel map. The f and g squares imply commutation with each d_r.
Step 3 (def-sp-convergence): induction in the cycle/boundary recursion shows that tE
preserves every finite Z_r and B_r and induces the page maps on Z_r/B_r. The universal
properties of the greatest lower bound and least upper bound give preservation of Z∞
and B∞. Restrict tE to Z∞ and use the cokernel universal property to descend to E∞.
Source: Stacks Project, Homological Algebra, Definitions 12.21.1 and 12.21.3,
Lemmas 12.21.2 and 12.21.4 (Tags 011Q, 011R, 011S, 011T)
(blueprint: lem-sp-derived-couple-functoriality). -/
theorem derivedCoupleFunctoriality (X Y : BigradedExactCouple C 0)
    (T : CoupleMorphism X Y) :
    (∃ M : ∀ n : ℕ, CoupleMorphism (X.pageCouple n) (Y.pageCouple n),
      (∀ p q : ℤ, (M 0).tD p q = T.tD p q) ∧
      (∀ p q : ℤ, (M 0).tE p q = T.tE p q) ∧
      (∀ (n : ℕ) (p q : ℤ),
        (M (n + 1)).tD p q ≫ (Y.pageCouple n).derivedDInclusion p q =
          (X.pageCouple n).derivedDInclusion p q ≫ (M n).tD p q) ∧
      (∀ (n : ℕ) (p q : ℤ),
        ∃ k : kernel ((X.pageCouple n).d p q) ⟶
          kernel ((Y.pageCouple n).d p q),
          k ≫ kernel.ι ((Y.pageCouple n).d p q) =
            kernel.ι ((X.pageCouple n).d p q) ≫ (M n).tE p q ∧
          (X.pageCouple n).derivedEProjection p q ≫ (M (n + 1)).tE p q =
            k ≫ (Y.pageCouple n).derivedEProjection p q) ∧
      (∀ (n : ℕ) (p q : ℤ),
        (M n).tE p q ≫ (Y.pageCouple n).d p q =
          (X.pageCouple n).d p q ≫ (M n).tE (p + 2 + n) (q - 1 - n))) ∧
    (∀ (LX : LimitSubobjects X) (LY : LimitSubobjects Y),
      (∀ p q : ℤ,
        (LY.Z p q).Factors ((LX.Z p q).arrow ≫ T.tE p q) ∧
        (LY.B p q).Factors ((LX.B p q).arrow ≫ T.tE p q)) ∧
      (∀ p q : ℤ, ∃ (e : X.pageInfinity LX p q ⟶ Y.pageInfinity LY p q)
          (z : (LX.Z p q : C) ⟶ (LY.Z p q : C)),
        (LX.Z p q).arrow ≫ T.tE p q = z ≫ (LY.Z p q).arrow ∧
        z ≫ cokernel.π (Subobject.ofLE (LY.B p q) (LY.Z p q)
              (limitBoundary_le_cycle Y LY p q)) =
          cokernel.π (Subobject.ofLE (LX.B p q) (LX.Z p q)
              (limitBoundary_le_cycle X LX p q)) ≫ e)
    ) := by
  classical
  let M : ∀ n : ℕ, CoupleMorphism (X.pageCouple n) (Y.pageCouple n) :=
    fun n ↦ Nat.rec T (fun _ U ↦ nextMorphism U) n
  have hD : ∀ n p q,
      (M (n + 1)).tD p q ≫ (Y.pageCouple n).derivedDInclusion p q =
        (X.pageCouple n).derivedDInclusion p q ≫ (M n).tD p q :=
    fun n p q ↦ nextMorphism_inclusion (M n) p q
  have hE : ∀ n p q,
      ∃ k : kernel ((X.pageCouple n).d p q) ⟶ kernel ((Y.pageCouple n).d p q),
        k ≫ kernel.ι ((Y.pageCouple n).d p q) =
          kernel.ι ((X.pageCouple n).d p q) ≫ (M n).tE p q ∧
        (X.pageCouple n).derivedEProjection p q ≫ (M (n + 1)).tE p q =
          k ≫ (Y.pageCouple n).derivedEProjection p q :=
    fun n p q ↦ nextMorphism_projection (M n) p q
  have hd := fun n p q ↦ morphism_d (M n) p q
  refine ⟨⟨M, fun _ _ ↦ rfl, fun _ _ ↦ rfl, hD, hE, hd⟩, ?_⟩
  have hfinite := exactCoupleFiniteTransport X Y T.tE
    (fun n p q ↦ (M n).tE p q) (fun _ _ ↦ rfl) hd hE
  intro LX LY
  have hlimit : ∀ p q,
      (LY.Z p q).Factors ((LX.Z p q).arrow ≫ T.tE p q) ∧
      (LY.B p q).Factors ((LX.B p q).arrow ≫ T.tE p q) := by
    intro p q
    constructor
    · apply (factors_iff_image_le _ _).mpr
      apply (LY.Z_glb p q).2
      rintro _ ⟨r, rfl⟩
      apply (factors_iff_image_le _ _).mp
      have hz := (LX.Z_glb p q).1 (Set.mem_range_self r)
      have h := Subobject.factors_of_factors_right (Subobject.ofLE _ _ hz)
        (hfinite r p q).1
      simpa only [Subobject.ofLE_arrow_assoc] using h
    · apply (pullback_factors_iff _ _ _).mp
      apply Subobject.factors_of_le _ ((LX.B_lub p q).2 ?_)
        (Subobject.factors_self _)
      rintro _ ⟨r, rfl⟩
      apply Subobject.le_of_factors
      apply pullback_factors
      exact Subobject.factors_of_le _ ((LY.B_lub p q).1 (Set.mem_range_self r))
        (hfinite r p q).2
  refine ⟨hlimit, ?_⟩
  intro p q
  let z := (LY.Z p q).factorThru ((LX.Z p q).arrow ≫ T.tE p q) (hlimit p q).1
  let b := (LY.B p q).factorThru ((LX.B p q).arrow ≫ T.tE p q) (hlimit p q).2
  let ix := Subobject.ofLE (LX.B p q) (LX.Z p q) (limitBoundary_le_cycle X LX p q)
  let iy := Subobject.ofLE (LY.B p q) (LY.Z p q) (limitBoundary_le_cycle Y LY p q)
  have hz : z ≫ (LY.Z p q).arrow = (LX.Z p q).arrow ≫ T.tE p q :=
    Subobject.factorThru_arrow _ _ _
  have hb : b ≫ (LY.B p q).arrow = (LX.B p q).arrow ≫ T.tE p q :=
    Subobject.factorThru_arrow _ _ _
  have hzb : ix ≫ z = b ≫ iy := by
    apply (cancel_mono (LY.Z p q).arrow).mp
    simp only [Category.assoc, hz, iy, ix, Subobject.ofLE_arrow,
      Subobject.ofLE_arrow_assoc, hb]
  have hzero : ix ≫ (z ≫ cokernel.π iy) = 0 := by
    rw [← Category.assoc, hzb, Category.assoc, cokernel.condition, comp_zero]
  refine ⟨cokernel.desc ix (z ≫ cokernel.π iy) hzero, z, hz.symm, ?_⟩
  exact (cokernel.π_desc _ _ _).symm

end CategoryTheory.BigradedExactCouple
