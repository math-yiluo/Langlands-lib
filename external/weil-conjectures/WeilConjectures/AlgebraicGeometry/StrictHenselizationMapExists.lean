/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.ResidueField
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.RingTheory.ProEtale.HenselianLocalRing
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension

/-! # Existence of the local strict-henselization map

Source: Stacks Project, Tags 03PS, 04GU and 08HR
(blueprint: lem-weil-pbc-strict-henselization-map-exists).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
/-- Existence of a local map over the base with the prescribed pointed residue map.
Source: Stacks Project, paragraph after Tag 03PS, Tags 04GU and 08HR
(blueprint: lem-weil-pbc-strict-henselization-map-exists).

Proof: Put C = strictHenselization barT and let t : Spec Omega -> Spec C
be the given residue embedding. Its factorizations imply t followed by the
structural map is barT, and locality of the residue embedding makes its image
the closed point. The local-structure theorem makes C strictly henselian.
For each affine pointed etale neighbourhood V of barS, pull V back along
Spec C -> T -> S. Choose an affine chart through the marked point of the pullback,
with coordinate ring B and marked prime q. The local map C -> B_q is weakly etale.
Olivier's theorem (Stacks Tag 092Z), in
`Algebra.WeaklyEtale.bijective_of_isStrictlyHenselianLocalRing`, makes it an
isomorphism. Its inverse gives a section. The field-valued point's ring map
extends to B_q, so the section preserves that point, not just its underlying prime.
These sections give maps Spec C -> V over S preserving the chosen point.
Two such maps agree: the etale diagonal is open, the marked closed point lies
in its range, and every point of Spec C generalizes the closed point. Thus their
pair factors through the diagonal. This proves compatibility of the maps with
all transition morphisms. Conjugating by the affine spectrum identifications
gives a cone. The strict-henselization limit supplies u : Spec C -> Spec C_S;
full faithfulness of Spec supplies h : C_S -> C. Its composites with the cone
legs give the structural-map equality. Limit extensionality and the prescribed
pointed factorizations give t followed by u equal to the point defined by sigmaS,
hence the required equality of ring maps into Omega. Since that composite is
local, `isLocalHom_of_comp` proves h local. The extra hypotheses hOmegaS and
hOmegaT are unnecessary in this route because the pointed factorizations are
already supplied; their signatures are retained unchanged.
Source for the section argument: Stacks Tags 03QO and 092Z; the pointed
localization calculation also occurs inside
`WeilConjectures.AlgebraicGeometry.StrictlyHenselianOpenSectionsStalk` as a private proof.
-/
theorem strictHenselizationMapExists
    {S T : Scheme.{v}} (g : T ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (barT : Spec (.of Ω) ⟶ T) (barS : Spec (.of Ω) ⟶ S)
    (hbar : barS = barT ≫ g)
    [Algebra (S.residueField (barS (IsLocalRing.closedPoint Ω))) Ω]
    [Algebra (T.residueField (barT (IsLocalRing.closedPoint Ω))) Ω]
    (hΩS : algebraMap (S.residueField (barS (IsLocalRing.closedPoint Ω))) Ω =
      (Scheme.descResidueField (Scheme.stalkClosedPointTo barS)).hom)
    (hΩT : algebraMap (T.residueField (barT (IsLocalRing.closedPoint Ω))) Ω =
      (Scheme.descResidueField (Scheme.stalkClosedPointTo barT)).hom)
    [IsLocalRing (Scheme.strictHenselization barS)]
    [IsLocalRing (Scheme.strictHenselization barT)]
    (σS : IsLocalRing.ResidueField (Scheme.strictHenselization barS) ≃+*
      separableClosure (S.residueField (barS (IsLocalRing.closedPoint Ω))) Ω)
    (σT : IsLocalRing.ResidueField (Scheme.strictHenselization barT) ≃+*
      separableClosure (T.residueField (barT (IsLocalRing.closedPoint Ω))) Ω)
    (hσS : ∀ j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barS),
      Spec.map (CommRingCat.ofHom
          (((IntermediateField.val
            (separableClosure (S.residueField (barS (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
              σS.toRingHom).comp
            (IsLocalRing.residue (Scheme.strictHenselization barS)))) ≫
          (Scheme.strictHenselizationAffineCone barS).π.app (Opposite.op (Opposite.op j)) ≫
            (Spec (Opposite.unop ((equivSmallModel.{v}
              (Scheme.strictHenselizationNeighbourhoods barS)).inverse.obj j).1.left)).isoSpec.inv =
        ((equivSmallModel.{v}
          (Scheme.strictHenselizationNeighbourhoods barS)).inverse.obj j).2.left)
    (hσT : ∀ j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barT),
      Spec.map (CommRingCat.ofHom
          (((IntermediateField.val
            (separableClosure (T.residueField (barT (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
              σT.toRingHom).comp
            (IsLocalRing.residue (Scheme.strictHenselization barT)))) ≫
          (Scheme.strictHenselizationAffineCone barT).π.app (Opposite.op (Opposite.op j)) ≫
            (Spec (Opposite.unop ((equivSmallModel.{v}
              (Scheme.strictHenselizationNeighbourhoods barT)).inverse.obj j).1.left)).isoSpec.inv =
        ((equivSmallModel.{v}
          (Scheme.strictHenselizationNeighbourhoods barT)).inverse.obj j).2.left) :
    ∃ h : Scheme.strictHenselization barS ⟶ Scheme.strictHenselization barT,
      IsLocalHom h.hom ∧
      Spec.map h ≫ Scheme.strictLocalizationToBase barS =
        Scheme.strictLocalizationToBase barT ≫ g ∧
      (((IntermediateField.val
          (separableClosure (S.residueField (barS (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
            σS.toRingHom).comp
          (IsLocalRing.residue (Scheme.strictHenselization barS))) =
        ((((IntermediateField.val
          (separableClosure (T.residueField (barT (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
            σT.toRingHom).comp
          (IsLocalRing.residue (Scheme.strictHenselization barT)))).comp h.hom := by
  classical
  let C := Scheme.strictHenselization barT
  let ψS := (((IntermediateField.val
    (separableClosure (S.residueField (barS (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
      σS.toRingHom).comp (IsLocalRing.residue (Scheme.strictHenselization barS)))
  let ψT := (((IntermediateField.val
    (separableClosure (T.residueField (barT (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
      σT.toRingHom).comp (IsLocalRing.residue C))
  let t := Spec.map (CommRingCat.ofHom ψT)
  let N := (equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barS)).inverse
  let D := (Scheme.strictHenselizationAffineDiagram barS).op ⋙ Scheme.Spec
  let p := fun j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barS) ↦
    ((Scheme.AffineEtale.Spec S).obj (N.obj j).1).hom
  let c := fun j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barS) ↦
    (Scheme.strictHenselizationAffineCone barS).π.app (Opposite.op (Opposite.op j)) ≫
      (Spec (Opposite.unop (N.obj j).1.left)).isoSpec.inv
  have hc : ∀ j, c j ≫ p j = Scheme.strictLocalizationToBase barS := by
    intro j
    simpa only [c, p, N, Scheme.isoSpec_Spec_inv] using!
      Scheme.strictHenselizationStructuralMap_eq barS j
  have htbase : t ≫ Scheme.strictLocalizationToBase barT = barT := by
    let := (Scheme.strictHenselizationAffineProperties barT).2.1
    let j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barT) :=
      Classical.choice IsCofiltered.nonempty
    have hj := Scheme.strictHenselizationStructuralMap_eq barT j
    have hp := hσT j
    have hw := ((equivSmallModel.{v}
      (Scheme.strictHenselizationNeighbourhoods barT)).inverse.obj j).2.w
    change t ≫ Scheme.strictLocalizationToBase barT = barT
    rw [← hj]
    simpa only [t, ψT, C, Scheme.isoSpec_Spec_inv, Category.assoc] using!
      (congrArg (fun f ↦ f ≫ ((Scheme.AffineEtale.Spec T).obj
        ((equivSmallModel.{v}
          (Scheme.strictHenselizationNeighbourhoods barT)).inverse.obj j).1).hom) hp).trans hw
  have htclosed : t default = IsLocalRing.closedPoint C := by
    change Spec.map (CommRingCat.ofHom ψT) default = _
    rw [Spec.map_apply]
    rw [Subsingleton.elim (default : Spec (.of Ω)) (IsLocalRing.closedPoint Ω)]
    exact IsLocalRing.comap_closedPoint ψT
  have hstrict : IsStrictlyHenselianLocalRing (Scheme.strictHenselization barT) :=
    ⟨inferInstance⟩
  let : IsStrictlyHenselianLocalRing C := hstrict
  -- Pointed section construction: localize an affine etale chart at the marked prime.
  -- Olivier's theorem identifies that localization with C; the field map extends
  -- to the localization and therefore the section preserves the specified point.
  have pointedSection {X : Scheme.{v}} (f : X ⟶ Spec C) [AlgebraicGeometry.Etale f]
      (a : Spec (.of Ω) ⟶ X) (hat : a ≫ f = t) :
      ∃ σ : Spec C ⟶ X, σ ≫ f = 𝟙 _ ∧ t ≫ σ = a := by
    let R := C
    have ht : t default = IsLocalRing.closedPoint R := htclosed
    obtain ⟨B, j, hj, haj, _⟩ :=
      Scheme.exists_affine_mem_range_and_range_subset (x := a default) (U := ⊤) (by simp)
    let : IsOpenImmersion j := hj
    let l : Spec (.of Ω) ⟶ Spec B := IsOpenImmersion.lift j a (by
      rintro _ ⟨z, rfl⟩
      simpa only [Subsingleton.elim z default] using haj)
    have hl : l ≫ j = a := IsOpenImmersion.lift_fac j a _
    let φ : CommRingCat.of R ⟶ B := Spec.preimage (j ≫ f)
    have hφ : Spec.map φ = j ≫ f := Spec.map_preimage _
    have hφe : φ.hom.Etale := by
      rw [← HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale), hφ]
      infer_instance
    algebraize [φ.hom]
    let q : PrimeSpectrum B := l default
    have hq : q.asIdeal.comap φ.hom = IsLocalRing.maximalIdeal R := by
      have h : (Spec.map φ) q = IsLocalRing.closedPoint R := by
        rw [hφ]
        change (l ≫ (j ≫ f)) default = _
        rw [← Category.assoc, hl, hat]
        exact ht
      exact congrArg PrimeSpectrum.asIdeal h
    let Bq := Localization.AtPrime q.asIdeal
    have : Algebra.WeaklyEtale R B := inferInstance
    have : Algebra.WeaklyEtale R Bq := Algebra.WeaklyEtale.trans R B Bq
    have : IsLocalHom (algebraMap R Bq) := by
      refine ⟨fun z hz ↦ ?_⟩
      rw [IsScalarTower.algebraMap_apply R B Bq,
        IsLocalization.AtPrime.isUnit_to_map_iff Bq q.asIdeal] at hz
      by_contra hn
      exact hz (by
        have : z ∈ IsLocalRing.maximalIdeal R := hn
        rw [← hq] at this
        exact this)
    let er : R ≃+* Bq := RingEquiv.ofBijective (algebraMap R Bq)
      (Algebra.WeaklyEtale.bijective_of_isStrictlyHenselianLocalRing (R := R) (S := Bq))
    let ψ : B ⟶ CommRingCat.of R :=
      CommRingCat.ofHom (er.symm.toRingHom.comp (algebraMap B Bq))
    have hψ : φ ≫ ψ = 𝟙 _ := by
      ext z
      change er.symm (algebraMap B Bq (algebraMap R B z)) = z
      rw [← IsScalarTower.algebraMap_apply R B Bq]
      exact er.symm_apply_apply z
    let χ : B ⟶ CommRingCat.of Ω := Spec.preimage l
    let θ : CommRingCat.of R ⟶ CommRingCat.of Ω := Spec.preimage t
    have hχ : Spec.map χ = l := Spec.map_preimage _
    have hθ : Spec.map θ = t := Spec.map_preimage _
    have hφχ : φ ≫ χ = θ := by
      apply Spec.map_injective
      rw [Spec.map_comp, hχ, hφ, hθ, ← Category.assoc, hl, hat]
    have hunit : ∀ z : q.asIdeal.primeCompl, IsUnit (χ.hom z) := by
      intro z
      apply isUnit_iff_ne_zero.mpr
      intro hz
      apply z.property
      change z.val ∈ (l default).asIdeal
      rw [← hχ, Spec.map_apply]
      simpa only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, Scheme.default_asIdeal,
        Ideal.mem_bot] using hz
    let χq : Bq →+* Ω := IsLocalization.lift hunit
    have hχq : χq.comp (algebraMap R Bq) = θ.hom := by
      ext z
      rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply R B Bq,
        IsLocalization.lift_eq]
      exact congrArg (fun m : CommRingCat.of R ⟶ CommRingCat.of Ω ↦ m.hom z) hφχ
    have hψθ : ψ ≫ θ = χ := by
      ext z
      change θ.hom (er.symm (algebraMap B Bq z)) = χ.hom z
      rw [← hχq, RingHom.comp_apply]
      change χq (er (er.symm (algebraMap B Bq z))) = _
      rw [er.apply_symm_apply]
      exact IsLocalization.lift_eq hunit z
    refine ⟨Spec.map ψ ≫ j, ?_, ?_⟩
    · rw [Category.assoc, ← hφ, ← Spec.map_comp, hψ, Spec.map_id]
      rfl
    · rw [← hθ, ← Spec.map_comp_assoc, hψθ, hχ, hl]
  let b := Scheme.strictLocalizationToBase barT ≫ g
  have htb : t ≫ b = barS := by
    simp only [b, ← Category.assoc, htbase, ← hbar]
  have lifts (j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barS)) :
      ∃ l : Spec C ⟶ Spec (Opposite.unop (N.obj j).1.left),
        l ≫ p j = b ∧ t ≫ l = (N.obj j).2.left := by
    let a := pullback.lift (N.obj j).2.left t (by
      change (N.obj j).2.left ≫ p j = t ≫ b
      rw [htb]
      exact (N.obj j).2.w)
    obtain ⟨σ, hσ, ha⟩ := pointedSection (pullback.snd (p j) b) a (by simp [a])
    refine ⟨σ ≫ pullback.fst (p j) b, ?_, ?_⟩
    · rw [Category.assoc, pullback.condition, ← Category.assoc, hσ, Category.id_comp]
    · rw [← Category.assoc, ha]
      simp [a]
  choose l hlbase hlpoint using lifts
  let cone : Cone D :=
    { pt := Spec C
      π :=
        { app := fun j ↦ l j.unop.unop ≫
            (Spec (Opposite.unop (N.obj j.unop.unop).1.left)).isoSpec.hom
          naturality := by
            intro i j f
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
            symm
            apply (cancel_mono
              (Spec (Opposite.unop (N.obj j.unop.unop).1.left)).isoSpec.inv).1
            let w := Spec.map (N.map f.unop.unop).1.left.unop
            have hw : w ≫ p j.unop.unop = p i.unop.unop := (N.map f.unop.unop).1.w
            have hp : (N.obj i.unop.unop).2.left ≫ w = (N.obj j.unop.unop).2.left :=
              congrArg Over.Hom.left (N.map f.unop.unop).2
            have heq : l i.unop.unop ≫ w = l j.unop.unop := by
              let u := l i.unop.unop ≫ w
              let v := l j.unop.unop
              let f := p j.unop.unop
              let β := ψT
              have hbase : u ≫ f = v ≫ f := by
                dsimp [u, v, f]
                rw [Category.assoc, hw, hlbase, hlbase]
              have hpoint : Spec.map (CommRingCat.ofHom β) ≫ u =
                  Spec.map (CommRingCat.ofHom β) ≫ v := by
                dsimp [u, v, β]
                rw [← Category.assoc, hlpoint, hp, hlpoint]
              let d := pullback.lift u v hbase
              have hd : Spec.map (CommRingCat.ofHom β) ≫ d =
                  Spec.map (CommRingCat.ofHom β) ≫ u ≫ pullback.diagonal f := by
                apply pullback.hom_ext
                · simp [d]
                · simpa [d] using hpoint.symm
              have hclosed : d (IsLocalRing.closedPoint C) ∈ Set.range (pullback.diagonal f) := by
                refine ⟨u (IsLocalRing.closedPoint C), ?_⟩
                have hb : Spec.map (CommRingCat.ofHom β) (IsLocalRing.closedPoint Ω) =
                    IsLocalRing.closedPoint C := IsLocalRing.comap_closedPoint β
                simpa only [Scheme.Hom.comp_apply, hb] using!
                  (congrArg (fun q ↦ q (IsLocalRing.closedPoint Ω)) hd).symm
              have hrange : Set.range d ⊆ Set.range (pullback.diagonal f) := by
                rintro _ ⟨x, rfl⟩
                exact ((IsLocalRing.specializes_closedPoint x).map d.continuous).mem_open
                  (IsOpenImmersion.isOpen_range (pullback.diagonal f)) hclosed
              let l := IsOpenImmersion.lift (pullback.diagonal f) d hrange
              have hl : l ≫ pullback.diagonal f = d :=
                IsOpenImmersion.lift_fac (pullback.diagonal f) d hrange
              have hu := congrArg (fun q ↦ q ≫ pullback.fst f f) hl
              have hv := congrArg (fun q ↦ q ≫ pullback.snd f f) hl
              have hu' : l = u := by simpa [d] using hu
              have hv' : l = v := by simpa [d] using hv
              exact hu'.symm.trans hv'
            change (l i.unop.unop ≫
              (Spec (Opposite.unop (N.obj i.unop.unop).1.left)).isoSpec.hom) ≫
              Spec.map (Spec.map (N.map f.unop.unop).1.left.unop).appTop ≫
                (Spec (Opposite.unop (N.obj j.unop.unop).1.left)).isoSpec.inv = _
            have hn := congrArg Spec.map
              (Scheme.ΓSpecIso_inv_naturality (N.map f.unop.unop).1.left.unop)
            simp only [Spec.map_comp] at hn
            simp only [Scheme.isoSpec_Spec_hom, Scheme.isoSpec_Spec_inv]
            rw [← hn]
            simpa only [w, Category.assoc, ← Spec.map_comp_assoc, Iso.inv_hom_id,
              ← Spec.map_comp, Iso.hom_inv_id, Spec.map_id,
              Category.id_comp, Category.comp_id] using heq } }
  obtain ⟨lim⟩ := (Scheme.strictHenselizationAffineProperties barS).2.2
  let u := lim.lift cone
  let h := Spec.preimage u
  have hu : Spec.map h = u := Spec.map_preimage u
  have hul (j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barS)) :
      u ≫ c j = l j := by
    have hf := lim.fac cone (Opposite.op (Opposite.op j))
    have he := congrArg (fun q ↦ q ≫
      (Spec (Opposite.unop (N.obj j).1.left)).isoSpec.inv) hf
    simpa only [u, c, cone, Category.assoc, Iso.hom_inv_id, Category.comp_id] using he
  have hbase : Spec.map h ≫ Scheme.strictLocalizationToBase barS = b := by
    let := (Scheme.strictHenselizationAffineProperties barS).2.1
    let j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barS) :=
      Classical.choice IsCofiltered.nonempty
    rw [hu, ← hc j, ← Category.assoc, hul, hlbase]
  have hpoint : t ≫ u = Spec.map (CommRingCat.ofHom ψS) := by
    apply lim.hom_ext
    intro j
    apply (cancel_mono
      (Spec (Opposite.unop (N.obj j.unop.unop).1.left)).isoSpec.inv).1
    change (t ≫ u) ≫ c j.unop.unop = Spec.map (CommRingCat.ofHom ψS) ≫ c j.unop.unop
    rw [Category.assoc, hul, hlpoint]
    exact (hσS j.unop.unop).symm
  have hres : ψS = ψT.comp h.hom := by
    have he : CommRingCat.ofHom ψS = h ≫ CommRingCat.ofHom ψT := by
      apply Spec.map_injective
      rw [Spec.map_comp, hu]
      exact hpoint.symm
    exact congrArg CommRingCat.Hom.hom he
  have hlocal : IsLocalHom h.hom := by
    have : IsLocalHom (ψT.comp h.hom) := hres ▸ inferInstanceAs (IsLocalHom ψS)
    exact isLocalHom_of_comp h.hom ψT
  exact ⟨h, hlocal, hbase, hres⟩


end AlgebraicGeometry
