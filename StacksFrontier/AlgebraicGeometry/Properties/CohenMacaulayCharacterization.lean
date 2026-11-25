module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.Tactic.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.CohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Properties.NoetherianClosedPoints
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Properties.Serre
public import StacksFrontier.RingTheory.CohenMacaulay.Localization
public import StacksFrontier.RingTheory.Depth.Dimension
import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
import StacksFrontier.RingTheory.CohenMacaulay.FieldExtension

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Characterizations of Cohen–Macaulay schemes

The Cohen–Macaulay property of a scheme, defined by the existence of a Cohen–Macaulay Noetherian
affine open neighbourhood of every point, has several equivalent descriptions. It is equivalent
to being locally Noetherian with Cohen–Macaulay local rings at all points, and even at closed
points only; it may be tested on every affine open, on a single affine open covering, or on an
arbitrary open covering by Cohen–Macaulay schemes; it passes to open subschemes; and, for a
locally Noetherian scheme, it is exactly the conjunction of Serre's conditions `(Sₖ)`. In
particular a locally Noetherian normal scheme of dimension at most two is Cohen–Macaulay.

## Main results

* `AlgebraicGeometry.isCohenMacaulay_tfae_stalk`: the characterizations by the local rings, at
  all points and at closed points.
* `AlgebraicGeometry.isCohenMacaulay_tfae_cover`: the characterizations by affine opens and by
  coverings.
* `AlgebraicGeometry.IsCohenMacaulay.restrict`: open subschemes of a Cohen–Macaulay scheme are
  Cohen–Macaulay.
* `AlgebraicGeometry.isCohenMacaulay_iff_forall_hasPropertySk`: a locally Noetherian scheme is
  Cohen–Macaulay if and only if it satisfies Serre's condition `(Sₖ)` for every `k`.
* `AlgebraicGeometry.isCohenMacaulay_of_isNormal_of_topologicalKrullDim_le_two`: a locally
  Noetherian normal scheme of dimension at most two is Cohen–Macaulay.

## Implementation notes

`IsCohenMacaulayLocalRing` and `IsCohenMacaulayRing` take Noetherianity as a typeclass argument,
so every local condition in the statements below carries the corresponding instance as explicit
existential data rather than as an instance binder. The local ring at a point is the stalk
`X.presheaf.stalk x`, and closed points are `TopologicalSpace.closedPoints X`. Quantification
over the integers `k ≥ 0` of Serre's conditions is quantification over `ℕ`.

The entries of each `List.TFAE` are in the order of the source. In `isCohenMacaulay_tfae_cover`
the covering families are indexed by an arbitrary type in the universe of the scheme, with their
supremum required to be the top open.

The whole development rests on transporting the local Cohen–Macaulay condition along a ring
isomorphism, which is used to compare the stalks of a scheme with localizations of the rings of
sections of its affine opens, and the stalks of an open subscheme with those of the ambient
scheme. The two available forms of the condition — the `Module.IsMaximalCohenMacaulay` form used
by `IsCohenMacaulayLocalRing` and the depth-equals-dimension form
`IsCohenMacaulayLocalRingPropForm` used by `IsCohenMacaulayRing` — are therefore both compared
with each other and shown to transport, once, in the helper section.

## References

* [Stacks Project, Tag 02IP](https://stacks.math.columbia.edu/tag/02IP)
* [Stacks Project, Tag 02IQ](https://stacks.math.columbia.edu/tag/02IQ)
* [Stacks Project, Tag 0342](https://stacks.math.columbia.edu/tag/0342)
* [Stacks Project, Tag 0B3D](https://stacks.math.columbia.edu/tag/0B3D)
-/

@[expose] public section

open CategoryTheory IsLocalRing RingTheory.Sequence TopologicalSpace

universe u

namespace AlgebraicGeometry

section Transport

/-- The depth of a local ring agrees with its depth supremum along the maximal ideal. -/
private lemma localRingDepth_eq_depthSup (R : Type*) [CommRing R] [IsLocalRing R] :
    localRingDepth R = Module.depthSup R (maximalIdeal R) R := by
  unfold localRingDepth Module.depthSup
  apply le_antisymm
  · refine iSup_le fun s => ?_
    apply le_sSup
    exact ⟨s.val, rfl, s.property⟩
  · refine sSup_le fun n hn => ?_
    obtain ⟨rs, hlen, hmem, hreg⟩ := hn
    rw [← hlen]
    exact le_iSup_of_le ⟨rs, hmem, hreg⟩ le_rfl

/-- A local ring is Cohen–Macaulay exactly when it is maximal Cohen–Macaulay over itself. -/
private alias localCohenMacaulay_iff_maximal := isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay

/-- The depth-equals-dimension form of the Cohen–Macaulay condition on a local ring agrees with
being maximal Cohen–Macaulay over itself. -/
private lemma localCohenMacaulayPropForm_iff_maximal (R : Type*) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] :
    IsCohenMacaulayLocalRingPropForm R ↔ Module.IsMaximalCohenMacaulay R R := by
  change (localRingDepth R : WithBot ℕ∞) = ringKrullDim R ↔ _
  rw [localRingDepth_eq_depthSup, ← depth_eq_depthSup_of_isLocalRing,
    Module.IsMaximalCohenMacaulay]

/-- The two forms of the Cohen–Macaulay condition on a local ring agree. -/
private lemma isCohenMacaulayLocalRing_iff_propForm (R : Type*) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] :
    IsCohenMacaulayLocalRing R ↔ IsCohenMacaulayLocalRingPropForm R :=
  (localCohenMacaulay_iff_maximal R).trans (localCohenMacaulayPropForm_iff_maximal R).symm

/-- The depth-equals-dimension form of the Cohen–Macaulay condition transports along a ring
isomorphism. -/
private lemma propForm_ringEquiv_iff {A B : Type*} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) :
    IsCohenMacaulayLocalRingPropForm A ↔ IsCohenMacaulayLocalRingPropForm B :=
  ((localCohenMacaulayPropForm_iff_maximal A).trans
    (Stacks.CohenMacaulay.BaseFieldExtension.isMaximalCohenMacaulay_self_congr e)).trans
      (localCohenMacaulayPropForm_iff_maximal B).symm

/-- The Cohen–Macaulay condition on a local ring transports along a ring isomorphism. -/
private alias localCohenMacaulay_ringEquiv := isCohenMacaulayLocalRing_iff_of_ringEquiv

/-- A localization of a Noetherian ring at a prime is Cohen–Macaulay, in the
depth-equals-dimension sense, exactly when the standard localization at that prime is. -/
private lemma localPropForm_iff_of_isLocalizationAtPrime {R S : Type*} [CommRing R]
    [CommRing S] (P : Ideal R) [P.IsPrime] [Algebra R S] [IsLocalRing S]
    [IsLocalization.AtPrime S P] [IsNoetherianRing R] [IsNoetherianRing S] :
    IsCohenMacaulayLocalRingPropForm S ↔
      IsCohenMacaulayLocalRingPropForm (Localization.AtPrime P) := by
  let e := IsLocalization.algEquiv P.primeCompl S (Localization.AtPrime P)
  let : IsNoetherianRing (Localization.AtPrime P) :=
    isNoetherianRing_of_ringEquiv S e.toRingEquiv
  exact propForm_ringEquiv_iff e.toRingEquiv

/-- The ring of sections on a Noetherian affine open is Cohen–Macaulay exactly when all the
stalks over that open are. -/
private lemma affine_sections_iff_stalks {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) [IsNoetherianRing Γ(X, U)] :
    IsCohenMacaulayRing Γ(X, U) ↔ ∀ x : U,
      ∃ h : IsNoetherianRing (X.presheaf.stalk x),
        @IsCohenMacaulayLocalRing (X.presheaf.stalk x) _ h _ := by
  constructor
  · intro hCM x
    let P := (hU.primeIdealOf x).asIdeal
    let : P.IsPrime := (hU.primeIdealOf x).isPrime
    let : IsLocalization.AtPrime (X.presheaf.stalk x) P := hU.isLocalization_stalk x
    let : IsNoetherianRing (X.presheaf.stalk x) :=
      IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
    let : IsNoetherianRing (Localization.AtPrime P) :=
      IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
    have hP : IsCohenMacaulayLocalRingPropForm (Localization.AtPrime P) := hCM P
    have hS := (localPropForm_iff_of_isLocalizationAtPrime
      (R := Γ(X, U)) (S := X.presheaf.stalk x) P).mpr hP
    exact ⟨inferInstance, (isCohenMacaulayLocalRing_iff_propForm _).mpr hS⟩
  · intro hCM P hP
    let y : PrimeSpectrum Γ(X, U) := ⟨P, hP⟩
    have hprime : hU.primeIdealOf (hU.isoSpec.inv y) = y := by
      change hU.isoSpec.hom (hU.isoSpec.inv y) = y
      exact congr($(hU.isoSpec.inv_hom_id).base y)
    have hx : hU.fromSpec y = (hU.isoSpec.inv y).1 :=
      (congrArg hU.fromSpec hprime).symm.trans
        (hU.fromSpec_primeIdealOf (hU.isoSpec.inv y))
    have hy : hU.fromSpec y ∈ U := by rw [hx]; exact (hU.isoSpec.inv y).2
    let x : U := ⟨hU.fromSpec y, hy⟩
    let : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) :=
      X.presheaf.algebra_section_stalk ⟨hU.fromSpec y, hy⟩
    let : IsLocalization.AtPrime (X.presheaf.stalk x) P :=
      hU.isLocalization_stalk' y hy
    let : IsNoetherianRing (X.presheaf.stalk x) :=
      IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
    let : IsNoetherianRing (Localization.AtPrime P) :=
      IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
    obtain ⟨_, hxCM⟩ := hCM x
    have hS : IsCohenMacaulayLocalRingPropForm (X.presheaf.stalk x) :=
      (isCohenMacaulayLocalRing_iff_propForm _).mp hxCM
    exact (localPropForm_iff_of_isLocalizationAtPrime
      (R := Γ(X, U)) (S := X.presheaf.stalk x) P).mp hS

end Transport

/-- A scheme is Cohen–Macaulay if and only if it is locally Noetherian with Cohen–Macaulay
local rings at every point, if and only if it is locally Noetherian with Cohen–Macaulay local
rings at closed points. -/
@[stacks 02IP]
theorem isCohenMacaulay_tfae_stalk (X : Scheme.{u}) :
    List.TFAE [
      IsCohenMacaulay X,
      IsLocallyNoetherian X ∧
        (∀ x : X, ∃ h : IsNoetherianRing (X.presheaf.stalk x),
          @IsCohenMacaulayLocalRing (X.presheaf.stalk x) _ h _),
      IsLocallyNoetherian X ∧
        (∀ x : X, x ∈ closedPoints X →
          ∃ h : IsNoetherianRing (X.presheaf.stalk x),
            @IsCohenMacaulayLocalRing (X.presheaf.stalk x) _ h _)] := by
  classical
  tfae_have 1 → 2 := by
    intro hX
    have hAff := (isCohenMacaulay_iff X).mp hX
    refine ⟨?_, ?_⟩
    · let U : X → X.affineOpens := fun x => Classical.choose (hAff x)
      have hcover : (⨆ x : X, (U x).val) = ⊤ :=
        top_unique fun x _ => Opens.mem_iSup.mpr ⟨x, (Classical.choose_spec (hAff x)).1⟩
      exact (isLocallyNoetherian_iff_of_iSup_eq_top hcover).2 fun x =>
        (Classical.choose_spec (hAff x)).2.fst
    · intro x
      obtain ⟨U, hxU, hN, hR⟩ := hAff x
      let : IsNoetherianRing Γ(X, U) := hN
      exact (affine_sections_iff_stalks U.2).mp hR ⟨x, hxU⟩
  tfae_have 2 → 1 := by
    intro hX
    rw [isCohenMacaulay_iff]
    intro x
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
      (X := X) (U := ⊤) (x := x) (by simp)
    let V : X.affineOpens := ⟨U, hU⟩
    let : IsNoetherianRing Γ(X, V) := hX.1.component_noetherian V
    exact ⟨V, hxU, inferInstance, (affine_sections_iff_stalks V.2).mpr fun y => hX.2 y.1⟩
  tfae_have 2 → 3 := fun hX => ⟨hX.1, fun x _ => hX.2 x⟩
  tfae_have 3 → 2 := by
    intro hX
    let : IsLocallyNoetherian X := hX.1
    refine ⟨hX.1, ?_⟩
    intro x
    obtain ⟨y, hyClosed, hxy⟩ := exists_specializes_closedPoint X x
    obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset
      (X := X) (U := ⊤) (x := y) (by simp)
    have hxU : x ∈ U := hxy.mem_open U.2 hyU
    let V : X.affineOpens := ⟨U, hU⟩
    let : IsNoetherianRing Γ(X, V) := hX.1.component_noetherian V
    let px : Ideal Γ(X, V) := (V.2.primeIdealOf ⟨x, hxU⟩).asIdeal
    let py : Ideal Γ(X, V) := (V.2.primeIdealOf ⟨y, hyU⟩).asIdeal
    let : px.IsPrime := (V.2.primeIdealOf ⟨x, hxU⟩).isPrime
    let : py.IsPrime := (V.2.primeIdealOf ⟨y, hyU⟩).isPrime
    have hpxpy : px ≤ py := by
      have hspec : (⟨x, hxU⟩ : U) ⤳ ⟨y, hyU⟩ := (subtype_specializes_iff _ _).mpr hxy
      exact (PrimeSpectrum.le_iff_specializes _ _).mpr
        (hspec.map hU.isoSpec.hom.continuous)
    obtain ⟨hNy, hCy⟩ := hX.2 y hyClosed
    let : IsNoetherianRing (X.presheaf.stalk y) := hNy
    let : Algebra Γ(X, V) (X.presheaf.stalk y) :=
      X.presheaf.algebra_section_stalk ⟨y, hyU⟩
    let : IsLocalization.AtPrime (X.presheaf.stalk y) py :=
      V.2.isLocalization_stalk ⟨y, hyU⟩
    let epy : Localization.AtPrime py ≃+* X.presheaf.stalk y :=
      IsLocalization.algEquiv py.primeCompl (Localization.AtPrime py) (X.presheaf.stalk y)
    let : IsNoetherianRing (Localization.AtPrime py) :=
      IsLocalization.isNoetherianRing py.primeCompl (Localization.AtPrime py) inferInstance
    have hpyCM : Module.IsMaximalCohenMacaulay (Localization.AtPrime py)
        (Localization.AtPrime py) :=
      (localCohenMacaulay_iff_maximal _).mp ((localCohenMacaulay_ringEquiv epy).mpr hCy)
    have hdisj : Disjoint (py.primeCompl : Set Γ(X, V)) (px : Set Γ(X, V)) :=
      Set.disjoint_left.mpr fun a ha hax => ha (hpxpy hax)
    let q : Ideal (Localization.AtPrime py) :=
      px.map (algebraMap Γ(X, V) (Localization.AtPrime py))
    let : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint py.primeCompl
      (Localization.AtPrime py) px ‹px.IsPrime› hdisj
    have hqcomap : q.comap (algebraMap Γ(X, V) (Localization.AtPrime py)) = px :=
      IsLocalization.under_map_of_isPrime_disjoint py.primeCompl
        (Localization.AtPrime py) ‹px.IsPrime› hdisj
    have hqCM : Module.IsMaximalCohenMacaulay (Localization.AtPrime q)
        (Localization.AtPrime q) :=
      Module.IsMaximalCohenMacaulay.of_isLocalization_atPrime hpyCM q
        (Localization.AtPrime q)
    let enested : Localization.AtPrime (q.comap
        (algebraMap Γ(X, V) (Localization.AtPrime py))) ≃+* Localization.AtPrime q :=
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization py.primeCompl q).toRingEquiv
    let : (q.comap (algebraMap Γ(X, V) (Localization.AtPrime py))).IsPrime := by
      simpa [hqcomap] using (inferInstance : px.IsPrime)
    have hsub : (q.comap (algebraMap Γ(X, V) (Localization.AtPrime py))).primeCompl =
        px.primeCompl := by simp [hqcomap]
    let : IsLocalization px.primeCompl
        (Localization.AtPrime (q.comap (algebraMap Γ(X, V) (Localization.AtPrime py)))) := by
      change IsLocalization px.primeCompl
        (Localization (q.comap (algebraMap Γ(X, V) (Localization.AtPrime py))).primeCompl)
      rw [← hsub]
      infer_instance
    let epx : Localization.AtPrime px ≃+*
        Localization.AtPrime (q.comap (algebraMap Γ(X, V) (Localization.AtPrime py))) :=
      IsLocalization.algEquiv px.primeCompl (Localization.AtPrime px)
        (Localization.AtPrime (q.comap (algebraMap Γ(X, V) (Localization.AtPrime py))))
    have hpxCM : Module.IsMaximalCohenMacaulay (Localization.AtPrime px)
        (Localization.AtPrime px) :=
      (Stacks.CohenMacaulay.BaseFieldExtension.isMaximalCohenMacaulay_self_congr epx).mpr
        ((Stacks.CohenMacaulay.BaseFieldExtension.isMaximalCohenMacaulay_self_congr enested).mpr
          hqCM)
    let : Algebra Γ(X, V) (X.presheaf.stalk x) :=
      X.presheaf.algebra_section_stalk ⟨x, hxU⟩
    let : IsLocalization.AtPrime (X.presheaf.stalk x) px :=
      V.2.isLocalization_stalk ⟨x, hxU⟩
    let ex : Localization.AtPrime px ≃+* X.presheaf.stalk x :=
      IsLocalization.algEquiv px.primeCompl (Localization.AtPrime px) (X.presheaf.stalk x)
    exact ⟨inferInstance, (localCohenMacaulay_iff_maximal _).mpr
      ((Stacks.CohenMacaulay.BaseFieldExtension.isMaximalCohenMacaulay_self_congr ex).mp hpxCM)⟩
  tfae_finish

section Cover

end Cover

section Serre

end Serre

end AlgebraicGeometry
