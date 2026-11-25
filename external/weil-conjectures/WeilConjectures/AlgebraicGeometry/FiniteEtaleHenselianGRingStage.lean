/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.MorphismProperty.Comma
import WeilConjectures.AlgebraicGeometry.FiniteEtaleFiniteTypeClosedFibreStage
import WeilConjectures.RingTheory.FiniteTypeIntGRing
import WeilConjectures.RingTheory.HenselizationPairGRing
import WeilConjectures.RingTheory.HenselizationUniversalProperty
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# A compatible henselian G-ring stage for a finite étale closed-fibre cover

Source: Stacks Project, Tag 0GS2, proof, General case.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

-- Pasting base-change squares and using the quotient isomorphism identifies the closed fibres.
private theorem closedFibre_baseChange_iso
    {R B : Type u} [CommRing R] [CommRing B] (K : Ideal R) (η : R →+* B)
    (hη : Function.Bijective (Ideal.quotientMap (K.map η) η Ideal.le_comap_map))
    {X : Scheme.{u}} (h : X ⟶ Spec (.of R)) :
    ∃ e : pullback (pullback.snd h (Spec.map (CommRingCat.ofHom η)))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (K.map η)))) ≅
        pullback h (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))),
      e.hom ≫ pullback.fst h (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))) =
        pullback.fst _ _ ≫ pullback.fst h (Spec.map (CommRingCat.ofHom η)) ∧
      e.hom ≫ pullback.snd h (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))) =
        pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom
          (Ideal.quotientMap (K.map η) η Ideal.le_comap_map)) := by
  let qR := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))
  let qB := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (K.map η)))
  let t := Spec.map (CommRingCat.ofHom η)
  let r := Spec.map (CommRingCat.ofHom
    (Ideal.quotientMap (K.map η) η Ideal.le_comap_map))
  have hr : IsIso r := by
    let er := (RingEquiv.ofBijective
      (Ideal.quotientMap (K.map η) η Ideal.le_comap_map) hη).toCommRingCatIso
    change IsIso (Spec.map er.hom)
    infer_instance
  have heq : qB ≫ t = r ≫ qR := by
    dsimp [qB, t, r, qR]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  let a := pullbackLeftPullbackSndIso h t qB
  let m := pullback.map h (qB ≫ t) h qR (𝟙 X) r (𝟙 _)
    (by simp) (by simpa using heq)
  have : IsIso m := inferInstance
  refine ⟨a ≪≫ asIso m, ?_, ?_⟩
  · simp [a, m, qR, qB, t, r]
  · simp [a, m, qR, qB, t, r]

/-- A finite étale cover of the closed fibre descends to a proper scheme over a henselian
G-ring, with maps from the original scheme and its closed fibre that commute with the
closed-fibre inclusions. This constructs the stage only; it does not lift the cover.

Source: Stacks Project, Tag 0GS2, proof, General case, using Tags 0A0P, 01ZM, 01ZO,
07RP, 07PX, 0A02, 0A04 and 0AH3.
(blueprint: lem-weil-pbc-finite-etale-henselian-g-ring-stage).

Proof:
1. Approximate Y over Spec A by proper Y_i over Spec A_i, where the A_i are finitely
   generated over Z, with affine transitions and limit Y (Tag 0A0P). The affine
   bases have ring colimit A. Put I_i equal to the inverse image of I in A_i.
2. The quotients A_i/I_i have colimit A/I: every element lifts from a stage, and an
   element vanishes in A/I precisely when its representative belongs to I_i. The
   closed fibres Y_i,0 have affine transitions and limit Y_0, since spectra turn
   these ring colimits into limits and fibre products commute with limits.
3. Descend V to a finitely presented cover of some Y_i,0 by Tag 01ZM. By Tags 01ZO
   and 07RP and directedness, increase i until this cover is finite and étale.
4. Henselize (A_i,I_i), obtaining (B,J). The ring A_i is a Noetherian G-ring by
   Tag 07PX, so B is a G-ring by Tag 0AH3. Tag 0A02 gives a henselian pair and
   A_i/I_i isomorphic to B/J. The map A_i to A extends to B to A by the
   henselization universal property (also the specialization in Tag 0A04), and
   this extension sends J into I.
5. Put Z = Y_i times Spec B over Spec A_i and let g be its proper projection.
   Pullback universality gives s : Y to Z from the limit projection and B to A.
   The quotient isomorphism identifies the closed fibre of Z with Y_i,0;
   transport the descended cover across this identification to obtain W.
6. The induced quotient map B/J to A/I and the closed-fibre limit projection give
   k : Y_0 to Z_0. Both sides of j_Y followed by s = k followed by j_Z have the
   same projections to Y_i and Spec B, so they agree by pullback extensionality.
   Base change of the descended cover along k gives V, as an isomorphism over Y_0.
   No lifting theorem for arbitrary henselian pairs is used in these steps. -/
theorem exists_finiteEtale_henselian_gRing_stage
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f]
    (V : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤
      (pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsGRing B)
      (J : Ideal B) (_ : HenselianRing B J) (Z : Scheme.{u})
      (g : Z ⟶ Spec (.of B)) (_ : IsProper g) (s : Y ⟶ Z)
      (k : pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ⟶
        pullback g (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
      (W : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤
        (pullback g (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))),
      (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≫ s =
        k ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) ∧
      Nonempty (Over.mk (pullback.snd W.hom k) ≅ Over.mk V.hom) := by
  classical
  obtain ⟨R, hR, hft, α, X, h, hh, p, hp, q, U, hqfst, hqsnd, ⟨eU⟩⟩ :=
    exists_finiteEtale_finiteType_closedFibre_stage I f V
  let : CommRing R := hR
  let : Algebra.FiniteType ℤ R := hft
  let : IsProper h := hh
  let K := I.comap α
  obtain ⟨_, _, c, hc⟩ := RingTheory.pair_henselization R K
  let B := c.pt.right
  let η : R →+* B := c.pt.hom.hom
  let J := K.map η
  let : HenselianRing B J := hc.2.1
  have hGR : IsGRing B :=
    RingTheory.isGRing_of_pair_henselization R K c hc (isGRing_of_finiteType_int R)
  obtain ⟨β, hβα, hβJ, _⟩ :=
    RingTheory.henselization_universal_property R K c hc.1 A I α
      (Ideal.map_le_iff_le_comap.mpr le_rfl)
  let t := Spec.map (CommRingCat.ofHom η)
  let a := Spec.map (CommRingCat.ofHom α)
  let b := Spec.map (CommRingCat.ofHom β)
  let qA := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let qB := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  let r := Spec.map (CommRingCat.ofHom (Ideal.quotientMap J η Ideal.le_comap_map))
  let n := Spec.map (CommRingCat.ofHom
    (Ideal.quotientMap I β (Ideal.map_le_iff_le_comap.mp hβJ)))
  let Z := pullback h t
  let g : Z ⟶ Spec (.of B) := pullback.snd h t
  have hbt : b ≫ t = a := by
    dsimp [b, t, a]
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext hβα
  let s : Y ⟶ Z := pullback.lift p (f ≫ b) (by
    rw [Category.assoc, hbt]
    exact hp)
  obtain ⟨e, hefst, hesnd⟩ := closedFibre_baseChange_iso K η hc.2.2 h
  let k : pullback f qA ⟶ pullback g qB := q ≫ e.inv
  have hr : IsIso r := by
    let er := (RingEquiv.ofBijective
      (Ideal.quotientMap J η Ideal.le_comap_map) hc.2.2).toCommRingCatIso
    change IsIso (Spec.map er.hom)
    infer_instance
  have hnr : n ≫ r = Spec.map (CommRingCat.ofHom (Ideal.quotientMap I α le_rfl)) := by
    dsimp [n, r]
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext x
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    exact congrArg (Ideal.Quotient.mk I) (RingHom.congr_fun hβα x)
  have hnb : n ≫ qB = qA ≫ b := by
    dsimp [n, qB, qA, b]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  have hksnd : k ≫ pullback.snd g qB = pullback.snd f qA ≫ n := by
    apply (cancel_mono r).1
    dsimp [k]
    simp only [Category.assoc]
    rw [← hesnd]
    simp only [Iso.inv_hom_id_assoc]
    rw [← Category.assoc, hqsnd, Category.assoc, hnr]
  have hsk : pullback.fst f qA ≫ s = k ≫ pullback.fst g qB := by
    apply pullback.hom_ext
    · dsimp [k, s, g]
      simp only [Category.assoc, pullback.lift_fst]
      rw [← hefst]
      simp only [Iso.inv_hom_id_assoc]
      exact hqfst
    · simp only [Category.assoc]
      change pullback.fst f qA ≫ s ≫ g = k ≫ pullback.fst g qB ≫ g
      rw [pullback.condition]
      simp only [s, g, pullback.lift_snd]
      change (pullback.fst f qA ≫ f) ≫ b = k ≫ pullback.snd g qB ≫ qB
      rw [← Category.assoc k, hksnd]
      simp only [Category.assoc]
      rw [hnb]
      exact pullback.condition_assoc b
  have : IsFinite U.hom := U.prop.1
  have : Etale U.hom := U.prop.2
  let W : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ (pullback g qB) :=
    MorphismProperty.Over.mk ⊤ (pullback.snd U.hom e.hom) ⟨inferInstance, inferInstance⟩
  refine ⟨B, inferInstance, hGR, J, inferInstance, Z, g, inferInstance, s, k, W, hsk, ?_⟩
  have hk : k ≫ e.hom = q := by simp [k]
  let d := pullback.congrHom (rfl : U.hom = U.hom) hk
  let z := pullbackLeftPullbackSndIso U.hom e.hom k
  exact ⟨Over.isoMk (z ≪≫ d) (by simp [z, d, W]; rfl) ≪≫ eU⟩

end AlgebraicGeometry.Scheme
