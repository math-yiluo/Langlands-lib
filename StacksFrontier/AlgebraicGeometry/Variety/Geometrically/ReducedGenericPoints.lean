module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Reduced
public import StacksFrontier.FieldTheory.Separable.TFAE
public import StacksFrontier.RingTheory.GeometricallyReduced.Basic
public import StacksFrontier.RingTheory.Nilpotent.GeometricallyReduced
public import StacksFrontier.RingTheory.Spectrum.Prime.IrreducibleComponents
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Geometric reducedness and generic points

Geometric reducedness at a point of a scheme over a field is inherited by generalizations of
that point. Conversely, at a point whose local ring is reduced it is implied by geometric
reducedness at the generic points of the irreducible components specializing to it; for a
reduced scheme this reduces the whole property to the generic points.

## Main results

* `AlgebraicGeometry.isGeometricallyReducedAt_of_specializes`: geometric reducedness at a point
  is preserved under generalization.
* `AlgebraicGeometry.isGeometricallyReducedAt_of_isReduced_stalk_of_genericPoints` gives
  geometric reducedness at a point from reducedness of its local ring and geometric reducedness
  at the relevant generic points.
* `AlgebraicGeometry.geometricallyReduced_of_isGeometricallyReducedAt_genericPoints` deduces
  geometric reducedness of a reduced scheme from geometric reducedness at all generic points.
* `AlgebraicGeometry.geometricallyReduced_iff_isSeparableExtension_functionField` characterises
  geometric reducedness of an integral scheme by separability of its function field.

## Implementation notes

Specialization is Mathlib's relation `x' ⤳ x`, and the generic points of the irreducible
components are Mathlib's `genericPoints`. Geometric reducedness at a point is
`AlgebraicGeometry.IsGeometricallyReducedAt`.

## References

* [Stacks Project, Tag 04KS](https://stacks.math.columbia.edu/tag/04KS)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

open scoped TensorProduct

universe u

/-- The structure maps from `k` to the stalks of a scheme over `k` commute with the
specialization maps between stalks. -/
private lemma stalkMap_comp_algebraMap_stalkSpecializes
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {x' x : X} (hsp : x' ⤳ x) :
    letI : Algebra k ((Spec (.of k)).presheaf.stalk (f.base x)) :=
      StructureSheaf.stalkAlgebra k (f.base x)
    letI : Algebra k ((Spec (.of k)).presheaf.stalk (f.base x')) :=
      StructureSheaf.stalkAlgebra k (f.base x')
    (f.stalkMap x').hom.comp (algebraMap k ((Spec (.of k)).presheaf.stalk (f.base x'))) =
      (X.presheaf.stalkSpecializes hsp).hom.comp
        ((f.stalkMap x).hom.comp (algebraMap k ((Spec (.of k)).presheaf.stalk (f.base x)))) := by
  let : Algebra k ((Spec (.of k)).presheaf.stalk (f.base x)) :=
    StructureSheaf.stalkAlgebra k (f.base x)
  let : Algebra k ((Spec (.of k)).presheaf.stalk (f.base x')) :=
    StructureSheaf.stalkAlgebra k (f.base x')
  ext a
  simp only [RingHom.coe_comp, Function.comp_apply]
  have hnaturality := Scheme.Hom.stalkSpecializes_stalkMap f x' x hsp
  have hbase := StructureSheaf.toStalk_stalkSpecializes (R := k) (hsp.map f.continuous)
  have hbase_a := congr_arg (fun g : CommRingCat.of k ⟶ _ ↦ g.hom a) hbase
  calc
    _ = (f.stalkMap x').hom
        (((Spec (.of k)).presheaf.stalkSpecializes (hsp.map f.continuous)).hom
          (algebraMap k ((Spec (.of k)).presheaf.stalk (f.base x)) a)) := by
            congr 1
            exact hbase_a.symm
    _ = _ := congr_arg (fun g :
        (Spec (.of k)).presheaf.stalk (f.base x) ⟶ X.presheaf.stalk x' ↦ g.hom
        (algebraMap k ((Spec (.of k)).presheaf.stalk (f.base x)) a)) hnaturality

/-- In a quasi-sober space, a point with no proper generalization is the generic point of an
irreducible component. -/
private lemma mem_genericPoints_of_forall_generalization_eq
    {T : Type*} [TopologicalSpace T] [QuasiSober T] (z : T)
    (hz : ∀ y : T, y ⤳ z → y = z) : z ∈ genericPoints T := by
  obtain ⟨Z, hZ, hsub⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible (closure ({z} : Set T))
      isIrreducible_singleton.closure
  have hzZ : z ∈ Z := hsub (subset_closure (Set.mem_singleton z))
  obtain ⟨η, hη⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)
  change closure {z} ∈ irreducibleComponents T
  rwa [← hz η (hη.specializes hzZ), hη]

/-- The point of an affine open corresponding to a minimal prime of its ring of sections is the
generic point of an irreducible component. -/
private lemma mem_genericPoints_of_primeIdealOf_mem_minimalPrimes {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (y : U) (hy : (hU.primeIdealOf y).asIdeal ∈ minimalPrimes Γ(X, U)) :
    (y : X) ∈ genericPoints X := by
  let e : U ≃ₜ PrimeSpectrum Γ(X, U) := Scheme.homeoOfIso hU.isoSpec
  refine mem_genericPoints_of_forall_generalization_eq _ fun z hz ↦ ?_
  let zU : U := ⟨z, hz.mem_open U.2 y.2⟩
  have hs : hU.primeIdealOf zU ⤳ hU.primeIdealOf y :=
    ((subtype_specializes_iff zU y).mpr hz).map e.continuous
  have hle : (hU.primeIdealOf zU).asIdeal ≤ (hU.primeIdealOf y).asIdeal :=
    (PrimeSpectrum.le_iff_specializes _ _).mpr hs
  exact congr_arg Subtype.val (e.injective (PrimeSpectrum.ext
    (le_antisymm hle (hy.2 ⟨(hU.primeIdealOf zU).isPrime, bot_le⟩ hle))))

/-- A minimal prime of a localization `S` of `R` at a prime `p` contracts to a minimal prime of
`R` contained in `p`. -/
private lemma comap_mem_minimalPrimes_of_isLocalization_atPrime {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime S p]
    {q : Ideal S} (hq : q.IsPrime) (hqmin : q ∈ minimalPrimes S) :
    q.comap (algebraMap R S) ≤ p ∧ q.comap (algebraMap R S) ∈ minimalPrimes R := by
  have hrle : q.comap (algebraMap R S) ≤ p := by
    have hd := (IsLocalization.isPrime_iff_isPrime_disjoint p.primeCompl S q).mp hq
    intro a ha
    by_contra hap
    exact (Set.disjoint_left.mp hd.2) hap ha
  refine ⟨hrle, ⟨hq.comap _, bot_le⟩, fun J hJ hJr ↦ ?_⟩
  have hdisj : Disjoint (p.primeCompl : Set R) (J : Set R) :=
    Set.disjoint_left.mpr fun a hap haJ ↦ hap (hJr.trans hrle haJ)
  have hmaple : J.map (algebraMap R S) ≤ q := Ideal.map_le_iff_le_comap.mpr hJr
  have hmapeq : J.map (algebraMap R S) = q := le_antisymm hmaple (hqmin.2
    ⟨IsLocalization.isPrime_of_isPrime_disjoint p.primeCompl S J hJ.1 hdisj, bot_le⟩ hmaple)
  rw [← IsLocalization.under_map_of_isPrime_disjoint p.primeCompl S hJ.1 hdisj, hmapeq]

/-- If `S` is the localization of `R` at a prime `p` and `T` is a localization of `S` at the image
of the complement of the contraction of a prime `q` of `S`, then `T` is the localization of `S`
at `q`. -/
private lemma isLocalization_atPrime_of_comap {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra S T] (p : Ideal R) [p.IsPrime]
    [IsLocalization.AtPrime S p] (q : Ideal S) [hq : q.IsPrime]
    [IsLocalization (Submonoid.map (algebraMap R S) (q.comap (algebraMap R S)).primeCompl) T] :
    IsLocalization.AtPrime T q := by
  refine IsLocalization.isLocalization_of_is_exists_mul_mem T
    (Submonoid.map (algebraMap R S) (q.comap (algebraMap R S)).primeCompl) q.primeCompl
    (by rintro _ ⟨a, ha, rfl⟩ haq; exact ha haq) ?_
  rintro ⟨a, ha⟩
  obtain ⟨⟨b, c⟩, hab⟩ := IsLocalization.surj p.primeCompl a
  have hbq : algebraMap R S b ∉ q := by
    intro hbq
    have hamul : a * algebraMap R S (c : R) ∈ q := hab.symm ▸ hbq
    exact (hq.mem_or_mem hamul).elim ha fun hcq ↦
      hq.ne_top (q.eq_top_of_isUnit_mem hcq (IsLocalization.map_units S c))
  exact ⟨algebraMap R S (c : R), b, hbq, by simpa [mul_comm] using hab.symm⟩

/-- If `y ⤳ x` lie in an affine open `U` and the prime of `y` is the contraction of a prime `q`
of the local ring at `x`, then geometric reducedness at `y` makes the localization of that local
ring at `q` geometrically reduced. -/
private lemma isGeometricallyReduced_localization_of_isGeometricallyReducedAt
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hxU : x ∈ U) (y : U) (hsp : (y : X) ⤳ x)
    (q : Ideal (X.presheaf.stalk x)) [hq : q.IsPrime] :
    letI : Algebra k (X.presheaf.stalk x) :=
      letI : Algebra k ((Spec (.of k)).presheaf.stalk (f.base x)) :=
        StructureSheaf.stalkAlgebra k (f.base x)
      ((f.stalkMap x).hom.comp
        (algebraMap k ((Spec (.of k)).presheaf.stalk (f.base x)))).toAlgebra
    letI : Algebra Γ(X, U) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
    (hU.primeIdealOf y).asIdeal = q.comap (algebraMap Γ(X, U) (X.presheaf.stalk x)) →
    q.comap (algebraMap Γ(X, U) (X.presheaf.stalk x)) ≤ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal →
    IsGeometricallyReducedAt f y → Algebra.IsGeometricallyReduced k (Localization.AtPrime q) := by
  intro hy hle hgeo
  let R := Γ(X, U)
  let S := X.presheaf.stalk x
  let T := X.presheaf.stalk (y : X)
  let : Algebra k ((Spec (.of k)).presheaf.stalk (f.base x)) :=
    StructureSheaf.stalkAlgebra k (f.base x)
  let : Algebra k S :=
    ((f.stalkMap x).hom.comp
      (algebraMap k ((Spec (.of k)).presheaf.stalk (f.base x)))).toAlgebra
  let : Algebra R S := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  let p : Ideal R := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  let r : Ideal R := q.comap (algebraMap R S)
  have : r.IsPrime := hq.comap _
  have : IsLocalization.AtPrime S p := hU.isLocalization_stalk ⟨x, hxU⟩
  let : Algebra k ((Spec (.of k)).presheaf.stalk (f.base y)) :=
    StructureSheaf.stalkAlgebra k (f.base y)
  let : Algebra k T :=
    ((f.stalkMap y).hom.comp
      (algebraMap k ((Spec (.of k)).presheaf.stalk (f.base y)))).toAlgebra
  have : Algebra.IsGeometricallyReduced k T :=
    (isGeometricallyReducedAt_iff_isGeometricallyReduced_stalk f y).mp hgeo
  let : Algebra R T := X.presheaf.algebra_section_stalk y
  have : IsLocalization.AtPrime T r := by
    simpa only [hy] using hU.isLocalization_stalk y
  have hpr : p.primeCompl ≤ r.primeCompl := fun a ha har ↦ ha (hle har)
  let : Algebra S T :=
    IsLocalization.localizationAlgebraOfSubmonoidLe S T p.primeCompl r.primeCompl hpr
  have : IsScalarTower R S T :=
    IsLocalization.localization_isScalarTower_of_submonoid_le S T p.primeCompl r.primeCompl hpr
  have : IsLocalization (Submonoid.map (algebraMap R S) r.primeCompl) T :=
    IsLocalization.isLocalization_of_submonoid_le S T p.primeCompl r.primeCompl hpr
  have : IsLocalization.AtPrime T q := isLocalization_atPrime_of_comap p q
  have hST : algebraMap S T = (X.presheaf.stalkSpecializes hsp).hom := by
    apply IsLocalization.ringHom_ext p.primeCompl
    rw [← IsScalarTower.algebraMap_eq R S T]
    exact congr_arg CommRingCat.Hom.hom
      (TopCat.Presheaf.germ_stalkSpecializes X.presheaf hxU hsp).symm
  have : IsScalarTower k S T := IsScalarTower.of_algebraMap_eq' (by
    rw [hST]
    exact stalkMap_comp_algebraMap_stalkSpecializes f hsp)
  let eK : T ≃ₐ[k] Localization.AtPrime q :=
    (IsLocalization.algEquiv q.primeCompl T (Localization.AtPrime q)).restrictScalars k
  exact Algebra.IsGeometricallyReduced.of_injective
    (f := eK.symm.toAlgHom) eK.symm.injective

/-- **Stacks Project, Tag 04KS.** A scheme over a field is geometrically reduced at a point
whose local ring is reduced if it is geometrically reduced at every generic point of an
irreducible component specializing to that point. -/
@[stacks 04KS "geometric_reducedness_at_point_of_generic_points"]
public theorem isGeometricallyReducedAt_of_isReduced_stalk_of_genericPoints
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X)
    (hx : _root_.IsReduced (X.presheaf.stalk x))
    (hgeneric : ∀ x' : X, x' ∈ genericPoints X → x' ⤳ x →
      IsGeometricallyReducedAt f x') :
    IsGeometricallyReducedAt f x := by
  rw [isGeometricallyReducedAt_iff_isGeometricallyReduced_stalk]
  let : Algebra k (X.presheaf.stalk x) :=
    let : Algebra k ((Spec (.of k)).presheaf.stalk (f.base x)) :=
      StructureSheaf.stalkAlgebra k (f.base x)
    ((f.stalkMap x).hom.comp
      (algebraMap k ((Spec (.of k)).presheaf.stalk (f.base x)))).toAlgebra
  let S := X.presheaf.stalk x
  have : _root_.IsReduced S := hx
  apply Algebra.IsGeometricallyReduced.of_forall_minimalPrimes
  intro q hq hqmin
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let R := Γ(X, U)
  let p : Ideal R := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  let : Algebra R S := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have : IsLocalization.AtPrime S p := hU.isLocalization_stalk ⟨x, hxU⟩
  let r : Ideal R := q.comap (algebraMap R S)
  obtain ⟨hrle, hrmin⟩ := comap_mem_minimalPrimes_of_isLocalization_atPrime p hq hqmin
  let yr : PrimeSpectrum R := ⟨r, hq.comap _⟩
  let e : U ≃ₜ PrimeSpectrum R := Scheme.homeoOfIso hU.isoSpec
  let xU : U := e.symm yr
  have hprime_xU : (hU.primeIdealOf xU).asIdeal = r := by
    change (e xU).asIdeal = r
    simp [xU, yr]
  have hxU_spec : (xU : X) ⤳ x := by
    have hs' : xU ⤳ (⟨x, hxU⟩ : U) := by
      apply e.isInducing.specializes_iff.mp
      rw [show e xU = yr by simp [xU],
        show e ⟨x, hxU⟩ = hU.primeIdealOf ⟨x, hxU⟩ from rfl]
      exact (PrimeSpectrum.le_iff_specializes yr _).mp hrle
    exact (subtype_specializes_iff xU ⟨x, hxU⟩).mp hs'
  have hxU_generic : (xU : X) ∈ genericPoints X :=
    mem_genericPoints_of_primeIdealOf_mem_minimalPrimes hU xU (by rw [hprime_xU]; exact hrmin)
  exact isGeometricallyReduced_localization_of_isGeometricallyReducedAt f hU hxU xU hxU_spec q
    hprime_xU hrle (hgeneric xU hxU_generic hxU_spec)

/-- A reduced scheme over a field which is geometrically reduced at the generic points of all
its irreducible components is geometrically reduced. -/
@[stacks 04KS "geometric_reducedness_of_generic_points"]
public lemma geometricallyReduced_of_isGeometricallyReducedAt_genericPoints
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsReduced X]
    (h : ∀ x : X, x ∈ genericPoints X → IsGeometricallyReducedAt f x) :
    GeometricallyReduced f :=
  (geometricallyReduced_iff_forall_isGeometricallyReducedAt f).2 fun x ↦
    isGeometricallyReducedAt_of_isReduced_stalk_of_genericPoints f x
      inferInstance fun x' hx' _ ↦ h x' hx'

/-! ### The function field of an integral scheme -/

end AlgebraicGeometry
