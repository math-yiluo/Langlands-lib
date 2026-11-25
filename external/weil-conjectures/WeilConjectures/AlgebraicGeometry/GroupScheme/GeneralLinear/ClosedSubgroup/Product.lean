/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
public import Mathlib.RingTheory.Spectrum.Prime.Jacobson
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup.LieSubalgebra
public import WeilConjectures.Mathlib.Algebra.Lie.Semisimple.Lemmas
public import WeilConjectures.Mathlib.RepresentationTheory.Subrepresentation
public import WeilConjectures.Mathlib.Topology.Constructible

/-!
# The central–geometric product `G° = Z(G°)° H°`

Let `H = V(J) ⊆ G = V(I)` be closed subgroups of `GL_n` over an algebraically closed field `k` of
characteristic zero such that `H` contains the commutators of `G` and `G°` acts semisimply on `kⁿ`.
Then every point of `G°(k)` is a product `t h` of a point `t` of the identity component `T` of the
centre of `G°` and a point `h` of `H°`.

The Lie algebra `𝔤` of `G°` acts faithfully and semisimply on `kⁿ` (a subspace is `G°`-stable if
and only if it is `𝔤`-stable), so `𝔤 = 𝔷(𝔤) + [𝔤, 𝔤]`; the brackets are tangent to `H°` and the
centre `𝔷(𝔤)` is the Lie algebra of `T`. The subgroup `K = T(k) H°(k)` thus has a closure with Lie
algebra `𝔤`, which is all of the connected `G°`. Finally `K` is closed: it is the image of
`T × H°` under multiplication, which is constructible (Chevalley), and a subgroup containing a
dense open subset of its irreducible closure is closed.

## Main results

- `AlgebraicGeometry.GeneralLinearGroup.mem_of_mem_closure_of_isConstructible`: a subgroup of
  `GL n k` whose image in `Spec k[GL_n]` has a constructible set with the same irreducible closure
  contains every `k`-point of the closure.
- `AlgebraicGeometry.GeneralLinearGroup.exists_mul_eq_of_commutator_mem`: the central–geometric
  product on `k`-points.

## Blueprint

- `lemma-identity-component`: the central–geometric product.
- `lemma-connected-components-images-homomorphisms--2`: the image of a regular homomorphism is
closed (here, for the
  multiplication map `T × H° ⟶ G°`).
-/

@[expose] public section

universe u

open Topology Matrix.GeneralLinearGroup
open scoped Matrix commutatorElement TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

namespace AlgebraicGeometry.GeneralLinearGroup

variable {n : Type u} [Fintype n] [DecidableEq n] {k : Type u} [Field k]

/-! ### Subgroups with a constructible image -/

/-- **A subgroup containing a dense constructible set of its irreducible closure is closed.** Let
`S` be a subgroup of `GL n k`, `k` algebraically closed, and `Y` a constructible subset of
`Spec k[GL_n]` with the closure of `S`, whose `k`-points lie in `S`. If this closure is
irreducible, it contains no other `k`-points than those of `S`.

`Y` contains a dense open subset `U` of the closure `T`; for a `k`-point `x` of `T`, the open
subsets `U` and `x U⁻¹` of `T` meet in a `k`-point `z`, so that `x = z (z⁻¹ x) ∈ S`.
(blueprint: `lemma-connected-components-images-homomorphisms--2`) -/
theorem mem_of_mem_closure_of_isConstructible [IsAlgClosed k] {S : Subgroup (GL n k)}
    {Y : Set (PrimeSpectrum (CoordinateRing n k))} (hY : IsConstructible Y)
    (hYS : ∀ y : GL n k, toPrimeSpectrum y ∈ Y → y ∈ S)
    (hcl : closure Y = closure (toPrimeSpectrum '' (S : Set (GL n k))))
    (hirr : IsIrreducible (closure (toPrimeSpectrum '' (S : Set (GL n k)))))
    {x : GL n k} (hx : toPrimeSpectrum x ∈ closure (toPrimeSpectrum '' (S : Set (GL n k)))) :
    x ∈ S := by
  have : IsNoetherianRing (CoordinateRing n k) := Algebra.FiniteType.isNoetherianRing k _
  have : IsJacobsonRing (CoordinateRing n k) := isJacobsonRing_of_finiteType (A := k)
  set T := closure (toPrimeSpectrum '' (S : Set (GL n k)))
  have hST : toPrimeSpectrum '' (S : Set (GL n k)) ⊆ T := subset_closure
  have htrans (a b : GL n k) (ha : a ∈ S) (hb : b ∈ S) : translateHomeomorph a b '' T ⊆ T := by
    refine (image_closure_subset_closure_image (translateHomeomorph a b).continuous).trans
      (closure_mono ?_)
    rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨_, S.mul_mem (S.mul_mem ha hs) hb, (translateHomeomorph_toPrimeSpectrum a b s).symm⟩
  have hinvT : invHomeomorph '' T ⊆ T := by
    refine (image_closure_subset_closure_image invHomeomorph.continuous).trans (closure_mono ?_)
    rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨_, S.inv_mem hs, (invHomeomorph_toPrimeSpectrum s).symm⟩
  have htransT {t : GL n k} (ht : toPrimeSpectrum t ∈ T) :
      translateHomeomorph t 1 '' T ⊆ T := by
    refine (image_closure_subset_closure_image (translateHomeomorph t 1).continuous).trans
      (closure_minimal ?_ isClosed_closure)
    rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    have := htrans 1 s S.one_mem hs ⟨_, ht, rfl⟩
    rwa [translateHomeomorph_toPrimeSpectrum, one_mul, ← mul_one (t * s),
      ← translateHomeomorph_toPrimeSpectrum] at this
  obtain ⟨U, hU, hUT, hUY⟩ := exists_isOpen_inter_subset_of_isConstructible hY isClosed_closure
    (hcl ▸ hirr) rfl
  rw [hcl] at hUT hUY
  have hT_inv_mem (t : GL n k) (ht : toPrimeSpectrum t ∈ T) : toPrimeSpectrum t⁻¹ ∈ T :=
    hinvT ⟨_, ht, invHomeomorph_toPrimeSpectrum t⟩
  set Φ := invHomeomorph.trans (translateHomeomorph x 1)
  have hΦT : Φ '' T = T := by
    refine Set.Subset.antisymm ?_ fun p hp ↦ ⟨invHomeomorph (translateHomeomorph x⁻¹ 1 p), ?_, ?_⟩
    · rintro _ ⟨p, hp, rfl⟩
      exact htransT hx ⟨_, hinvT ⟨p, hp, rfl⟩, rfl⟩
    · exact hinvT ⟨_, htransT (hT_inv_mem x hx) ⟨p, hp, rfl⟩, rfl⟩
    · change translateHomeomorph x 1 (invHomeomorph (invHomeomorph _)) = p
      rw [invHomeomorph_invHomeomorph, translateHomeomorph_translateHomeomorph, mul_inv_cancel,
        mul_one, translateHomeomorph_one_one_apply]
  obtain ⟨p₀, hp₀U, hp₀T⟩ := hUT
  have hW : (T ∩ Φ '' U).Nonempty := by
    refine ⟨Φ p₀, ?_, Set.mem_image_of_mem Φ hp₀U⟩
    rw [← hΦT]
    exact Set.mem_image_of_mem Φ hp₀T
  obtain ⟨w, hwT, hwU, hwΦ⟩ := hirr.2 U (Φ '' U) hU (Φ.isOpenMap U hU) ⟨p₀, hp₀T, hp₀U⟩ hW
  obtain ⟨q, ⟨hqT, hqU, hqΦ⟩, hq⟩ := nonempty_inter_closedPoints (Z := T ∩ (U ∩ Φ '' U))
    ⟨w, hwT, hwU, hwΦ⟩ (isClosed_closure.isLocallyClosed.inter
      (hU.inter (Φ.isOpenMap U hU)).isLocallyClosed)
  obtain ⟨z, rfl⟩ := exists_toPrimeSpectrum_eq_of_mem_closedPoints hq
  have hz : z ∈ S := hYS z (hUY ⟨hqU, hqT⟩)
  obtain ⟨p, hpU, hpz⟩ := hqΦ
  have hp : p = toPrimeSpectrum (z⁻¹ * x) := by
    rw [← Φ.symm_apply_apply p, hpz]
    change invHomeomorph (translateHomeomorph x⁻¹ 1⁻¹ (toPrimeSpectrum z)) = _
    rw [translateHomeomorph_toPrimeSpectrum, invHomeomorph_toPrimeSpectrum]
    congr 1
    simp
  have hpT : p ∈ T := by
    rw [← hΦT] at hqT
    obtain ⟨p', hp'T, hp'⟩ := hqT
    rwa [← Φ.injective (hp'.trans hpz.symm)]
  have : z⁻¹ * x ∈ S := hYS _ (hUY ⟨hp ▸ hpU, hp ▸ hpT⟩)
  simpa using S.mul_mem hz this

/-! ### The Lie algebra of a group acting semisimply -/

section Lie

variable [IsAlgClosed k] [CharZero k] {I : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k]

/-- If a connected `G = V(I)` acts semisimply on `kⁿ`, then its Lie algebra `𝔤` is the sum of its
centre `𝔷(𝔤) = Lie Z(G)` and its derived algebra: every `X ∈ 𝔤` is the sum of a tangent vector of
`Z(G)` and an element of any subspace `M` containing the brackets of `𝔤`.

`kⁿ` is a faithful semisimple `𝔤`-module (its `𝔤`-stable subspaces are its `G`-stable ones), so
`𝔤` has central radical and `𝔤 = 𝔷(𝔤) + [𝔤, 𝔤]`.
(blueprint: `lemma-identity-component`,
`proposition-lie-algebras-faithful-semisimple-representation--1`) -/
theorem lieSubalgebra_le_center_sup [I.IsPrime]
    [hss : Representation.IsSemisimpleRepresentation
      ((toRepresentation n k).comp (zeroLocus I k).subtype)]
    (M : Submodule k (Matrix n n k))
    (hM : ∀ Y ∈ lieSubalgebra I, ∀ Y' ∈ lieSubalgebra I, ⁅Y, Y'⁆ ∈ M) :
    (lieSubalgebra I).toSubmodule ≤ (lieSubalgebra (center I)).toSubmodule ⊔ M := by
  set e := (lieEquivMatrix' (R := k) (n := n))
  set L := (lieSubalgebra I).map e.symm.toLieHom
  have hmemL {f : Module.End k (n → k)} : f ∈ L ↔ e f ∈ lieSubalgebra I := by
    rw [LieSubalgebra.mem_map]
    refine ⟨fun ⟨Y, hY, hYf⟩ ↦ ?_, fun h ↦ ⟨e f, h, by simp⟩⟩
    rw [← hYf]
    simpa using hY
  have he (f : Module.End k (n → k)) (v : n → k) : e f *ᵥ v = f v := by
    simp [e, ← Matrix.toLin'_apply]
  -- the subspaces stable under `L` are those stable under `G(k)`
  have hstab (U : Submodule k (n → k)) :
      (∀ x : L, ∀ m ∈ U, (x : Module.End k (n → k)) m ∈ U) ↔
        ∀ g : zeroLocus I k, ∀ m ∈ U,
          (toRepresentation n k).comp (zeroLocus I k).subtype g m ∈ U := by
    have key := forall_mulVec_mem_iff_forall_lieSubalgebra (I := I) U
    constructor
    · intro h g m hm
      refine key.2 (fun X hX u hu ↦ ?_) g g.2 m hm
      have := h ⟨e.symm X, hmemL.2 (by simpa using hX)⟩ u hu
      have h2 := he (e.symm X) u
      rw [LieEquiv.apply_symm_apply] at h2
      rw [h2]
      exact this
    · intro h x m hm
      have := key.1 (fun g hg u hu ↦ h ⟨g, hg⟩ u hu) _ (hmemL.1 x.2) m hm
      rwa [he] at this
  let iso : LieSubmodule k L (n → k) ≃o
      Subrepresentation ((toRepresentation n k).comp (zeroLocus I k).subtype) :=
    { toFun N := ⟨N.toSubmodule, (hstab N.toSubmodule).1 fun x _ hm ↦ N.lie_mem (x := x) hm⟩
      invFun U := { U.toSubmodule with
        lie_mem := fun {x m} hm ↦ (hstab U.toSubmodule).2
          (fun g _ hm ↦ U.apply_mem_toSubmodule g hm) x m hm }
      left_inv N := rfl
      right_inv U := rfl
      map_rel_iff' {N N'} := by
        change N.toSubmodule ≤ N'.toSubmodule ↔ _
        exact LieSubmodule.toSubmodule_le_toSubmodule _ _ }
  have : LieModule.IsSemisimple k L (n → k) := iso.complementedLattice_iff.2 hss
  have := LieAlgebra.hasCentralRadical_of_isFaithful k L (n → k)
  have htop := LieAlgebra.center_sup_derivedSeries_eq_top k L
  intro X hX
  set x : L := ⟨e.symm X, hmemL.2 (by simpa using hX)⟩
  have hx : x ∈ LieAlgebra.center k L ⊔ LieAlgebra.derivedSeries k L 1 := htop ▸ trivial
  obtain ⟨z, hz, d, hd, hzd⟩ := (LieSubmodule.mem_sup _ _ _).1 hx
  have hXe : X = e z + e d := by
    have := congrArg (fun y : L ↦ e (y : Module.End k (n → k))) hzd
    simp only [x, LieEquiv.apply_symm_apply] at this
    rw [← this]
    exact e.toLinearEquiv.map_add _ _
  rw [hXe]
  refine Submodule.add_mem_sup ?_ ?_
  · change e z ∈ lieSubalgebra (center I)
    rw [mem_lieSubalgebra_center_iff]
    refine ⟨hmemL.1 z.2, fun Y hY ↦ ?_⟩
    have hzY := (LieModule.mem_maxTrivSubmodule k L L z).1 hz
      ⟨e.symm Y, hmemL.2 (by simpa using hY)⟩
    have h1 : ((e.symm Y : Module.End k (n → k)) * z - z * e.symm Y : Module.End k (n → k)) =
        0 := by
      have := congrArg Subtype.val hzY
      rwa [LieSubalgebra.coe_bracket, Ring.lie_def] at this
    have e_mul (f g : Module.End k (n → k)) : e (f * g) = e f * e g := LinearMap.toMatrix'_mul f g
    have h2 := congrArg e h1
    rw [map_sub, map_zero, e_mul, e_mul, LieEquiv.apply_symm_apply, sub_eq_zero] at h2
    exact h2.symm
  · have hle : (LieAlgebra.derivedSeries k L 1 : Submodule k L) ≤
        M.comap (e.toLinearMap ∘ₗ (L.toSubmodule.subtype)) := by
      rw [LieAlgebra.coe_derivedSeries_one_eq, Submodule.span_le]
      rintro _ ⟨y, y', rfl⟩
      change e ((⁅y, y'⁆ : L) : Module.End k (n → k)) ∈ M
      rw [LieSubalgebra.coe_bracket, LieEquiv.map_lie]
      exact hM _ (hmemL.1 y.2) _ (hmemL.1 y'.2)
    exact hle hd

end Lie

/-! ### The product -/

section Product

variable [IsAlgClosed k] [CharZero k]

/-- The product `T(k) H(k)` of two subgroups of `GL n k`, the first commuting with the second, is a
subgroup. -/
def mulOfCommute (T H : Subgroup (GL n k)) (hTH : ∀ t ∈ T, ∀ h ∈ H, h * t = t * h) :
    Subgroup (GL n k) where
  carrier := {g | ∃ t ∈ T, ∃ h ∈ H, t * h = g}
  one_mem' := ⟨1, T.one_mem, 1, H.one_mem, mul_one 1⟩
  mul_mem' := by
    rintro _ _ ⟨t, ht, h, hh, rfl⟩ ⟨t', ht', h', hh', rfl⟩
    refine ⟨t * t', T.mul_mem ht ht', h * h', H.mul_mem hh hh', ?_⟩
    rw [mul_assoc, ← mul_assoc t', ← hTH t' ht' h hh, mul_assoc, mul_assoc]
  inv_mem' := by
    rintro _ ⟨t, ht, h, hh, rfl⟩
    refine ⟨t⁻¹, T.inv_mem ht, h⁻¹, H.inv_mem hh, ?_⟩
    rw [mul_inv_rev]
    exact (hTH _ (T.inv_mem ht) _ (H.inv_mem hh)).symm

omit [IsAlgClosed k] [CharZero k] in
theorem mem_mulOfCommute {T H : Subgroup (GL n k)} {hTH : ∀ t ∈ T, ∀ h ∈ H, h * t = t * h}
    {g : GL n k} : g ∈ mulOfCommute T H hTH ↔ ∃ t ∈ T, ∃ h ∈ H, t * h = g :=
  Iff.rfl

omit [IsAlgClosed k] [CharZero k] in
/-- The points of `V(I) × V(J)` with values in a field: a `k`-point of
`(k[GL_n] ⧸ I) ⊗ (k[GL_n] ⧸ J)` is a pair of points `(t, h)`, and the product of the universal pair
specializes to `t h`. -/
theorem exists_comp_evalAlgHom_mul_eq (I J : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]
    [J.IsHopfIdeal k]
    (χ : (CoordinateRing n k ⧸ I) ⊗[k] (CoordinateRing n k ⧸ J) →ₐ[k] k) :
    ∃ t ∈ zeroLocus I k, ∃ h ∈ zeroLocus J k,
      χ.comp (evalAlgHom (inlQuotient I J (genericUnit n k) *
        inrQuotient I J (genericUnit n k))) = evalAlgHom (t * h) := by
  set f := χ.comp (Algebra.TensorProduct.includeLeft.comp (Ideal.Quotient.mkₐ k I))
  set g := χ.comp (Algebra.TensorProduct.includeRight.comp (Ideal.Quotient.mkₐ k J))
  have hf : ∀ a ∈ I, f a = 0 := fun a ha ↦ by
    simp [f, Ideal.Quotient.eq_zero_iff_mem.2 ha]
  have hg : ∀ a ∈ J, g a = 0 := fun a ha ↦ by
    simp [g, Ideal.Quotient.eq_zero_iff_mem.2 ha]
  have hχ : χ = Algebra.TensorProduct.liftQuotient I J f g hf hg := by
    refine Algebra.TensorProduct.ext (Ideal.Quotient.algHom_ext k (AlgHom.ext fun a ↦ ?_))
      (Ideal.Quotient.algHom_ext k (AlgHom.ext fun a ↦ ?_))
    · change χ (Ideal.Quotient.mk I a ⊗ₜ[k] 1) = _
      rw [← map_one (Ideal.Quotient.mk J)]
      change _ = Algebra.TensorProduct.liftQuotient I J f g hf hg
        (Ideal.Quotient.mk I a ⊗ₜ[k] Ideal.Quotient.mk J 1)
      rw [Algebra.TensorProduct.liftQuotient_tmul, show g 1 = 1 from map_one g, mul_one, map_one]
      rfl
    · change χ (1 ⊗ₜ[k] Ideal.Quotient.mk J a) = _
      rw [← map_one (Ideal.Quotient.mk I)]
      change _ = Algebra.TensorProduct.liftQuotient I J f g hf hg
        (Ideal.Quotient.mk I 1 ⊗ₜ[k] Ideal.Quotient.mk J a)
      rw [Algebra.TensorProduct.liftQuotient_tmul, show f 1 = 1 from map_one f, one_mul, map_one]
      rfl
  refine ⟨Matrix.GeneralLinearGroup.map f.toRingHom (genericUnit n k), fun a ha ↦ ?_,
    Matrix.GeneralLinearGroup.map g.toRingHom (genericUnit n k), fun a ha ↦ ?_, ?_⟩
  · rw [evalAlgHom_map_genericUnit]
    exact hf a ha
  · rw [evalAlgHom_map_genericUnit]
    exact hg a ha
  · rw [← evalAlgHom_map, map_mul, hχ, map_liftQuotient_inlQuotient,
      map_liftQuotient_inrQuotient]

omit [IsAlgClosed k] [CharZero k] in
/-- Conversely, a pair of points `(t, h)` of `V(I) × V(J)` specializes the product of the
universal pair to `t h`. -/
theorem liftQuotient_comp_evalAlgHom_mul (I J : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]
    [J.IsHopfIdeal k] {t h : GL n k} (ht : t ∈ zeroLocus I k) (hh : h ∈ zeroLocus J k) :
    (Algebra.TensorProduct.liftQuotient I J (evalAlgHom t) (evalAlgHom h) ht hh).comp
      (evalAlgHom (inlQuotient I J (genericUnit n k) * inrQuotient I J (genericUnit n k))) =
        evalAlgHom (t * h) := by
  rw [← evalAlgHom_map, map_mul, map_liftQuotient_inlQuotient, map_liftQuotient_inrQuotient,
    map_evalAlgHom_genericUnit, map_evalAlgHom_genericUnit]

/-- **The central–geometric product**, on `k`-points. Let `H = V(J) ⊆ G = V(I)` be closed subgroups
of `GL_n` over an algebraically closed field of characteristic zero, such that the commutators of
`G` lie in `H` (over `k[ε₁][ε₂]`) and `G°` acts semisimply on `kⁿ`. Then every point of `G°(k)` is
a product `t h` of a point `t` of the identity component `T = Z(G°)°` of the centre of `G°` and a
point `h` of `H°`.

The Lie algebra of `G°` is `Lie T + Lie H°` (`lieSubalgebra_le_center_sup`), so the Zariski closure
of the subgroup `K = T(k) H°(k)` of `G°(k)` has the Lie algebra of the connected `G°`, hence is
`G°`; and `K`, the image of the multiplication `T × H° ⟶ G°`, is closed
(`mem_of_mem_closure_of_isConstructible`). (blueprint: `lemma-identity-component`) -/
theorem exists_mul_eq_of_commutator_mem {I J : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k]
    [J.IsHopfIdeal k] (hIJ : I ≤ J)
    (hcomm : ∀ g ∈ zeroLocus I (DualNumber (DualNumber k)),
      ∀ g' ∈ zeroLocus I (DualNumber (DualNumber k)), ⁅g, g'⁆ ∈ zeroLocus J _)
    [Representation.IsSemisimpleRepresentation
      ((toRepresentation n k).comp (zeroLocus (identityComponent I) k).subtype)]
    {g : GL n k} (hg : g ∈ zeroLocus (identityComponent I) k) :
    ∃ t ∈ zeroLocus (identityComponent (center (identityComponent I))) k,
      ∃ h ∈ zeroLocus (identityComponent J) k, t * h = g := by
  have : IsNoetherianRing (CoordinateRing n k) := Algebra.FiniteType.isNoetherianRing k _
  set G := identityComponent I
  have hGp : G.IsPrime := isPrime_identityComponent I
  set T := identityComponent (center G)
  set H := identityComponent J
  have hGH : G ≤ H := identityComponent_mono I hIJ
  -- the Lie algebra of `G°` is `Lie T + Lie H°`
  have hLie : (lieSubalgebra G).toSubmodule ≤
      (lieSubalgebra T).toSubmodule ⊔ (lieSubalgebra H).toSubmodule := by
    rw [lieSubalgebra_identityComponent (center G), lieSubalgebra_identityComponent J]
    refine lieSubalgebra_le_center_sup _ fun Y hY Y' hY' ↦ ?_
    rw [lieSubalgebra_identityComponent] at hY hY'
    exact lie_mem_lieSubalgebra_of_commutator_mem hcomm hY hY'
  -- the subgroup `K = T(k) H°(k)`
  have hT (t : GL n k) (ht : t ∈ zeroLocus T k) :
      t ∈ zeroLocus G k ∧ ∀ x ∈ zeroLocus G k, t * x = x * t :=
    (mem_zeroLocus_center_iff G).1 (zeroLocus_anti (le_identityComponent _) ht)
  set K := mulOfCommute (zeroLocus T k) (zeroLocus H k) fun t ht h hh ↦
    ((hT t ht).2 h (zeroLocus_anti hGH hh)).symm
  have hKG : (K : Set (GL n k)) ⊆ zeroLocus G k := by
    rintro _ ⟨t, ht, h, hh, rfl⟩
    exact (zeroLocus G k).mul_mem (hT t ht).1 (zeroLocus_anti hGH hh)
  set JK := vanishingIdeal (K : Set (GL n k))
  have hGJK : G ≤ JK :=
    (le_vanishingIdeal_zeroLocus G).trans (vanishingIdeal_anti hKG)
  have hJKT : JK ≤ T := (vanishingIdeal_anti fun t ht ↦
    (mem_mulOfCommute.2 ⟨t, ht, 1, one_mem _, mul_one t⟩ : t ∈ K)).trans
    (vanishingIdeal_zeroLocus_le_of_isRadical T (isRadical_identityComponent _))
  have hJKH : JK ≤ H := (vanishingIdeal_anti fun h hh ↦
    (mem_mulOfCommute.2 ⟨1, one_mem _, h, hh, one_mul h⟩ : h ∈ K)).trans
    (vanishingIdeal_zeroLocus_le_of_isRadical H (isRadical_identityComponent _))
  -- the closure of `K` is `G°`
  have hJK : JK = G := by
    refine eq_of_le_of_lieSubalgebra_eq hGJK (le_antisymm (lieSubalgebra_anti hGJK) ?_)
    intro X hX
    have := hLie hX
    rw [Submodule.mem_sup] at this
    obtain ⟨Y, hY, Z, hZ, rfl⟩ := this
    exact add_mem (lieSubalgebra_anti hJKT hY) (lieSubalgebra_anti hJKH hZ)
  -- `K` is the image of `T × H°`, hence closed
  set B := (CoordinateRing n k ⧸ T) ⊗[k] (CoordinateRing n k ⧸ H)
  have : Algebra.FiniteType k B :=
    Algebra.FiniteType.trans (S := CoordinateRing n k ⧸ T) inferInstance inferInstance
  have : IsJacobsonRing B := isJacobsonRing_of_finiteType (A := k)
  set φ : CoordinateRing n k →ₐ[k] B :=
    evalAlgHom (inlQuotient T H (genericUnit n k) * inrQuotient T H (genericUnit n k))
  set Y := Set.range (PrimeSpectrum.comap (φ : CoordinateRing n k →+* B))
  have hcomap (χ : B →ₐ[k] k) {x : GL n k} (hx : χ.comp φ = evalAlgHom x) :
      PrimeSpectrum.comap (φ : CoordinateRing n k →+* B)
        ⟨RingHom.ker χ, RingHom.ker_isPrime _⟩ = toPrimeSpectrum x := by
    ext a
    simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, RingHom.mem_ker, toPrimeSpectrum]
    rw [← hx]
    rfl
  have hKY : toPrimeSpectrum '' (K : Set (GL n k)) ⊆ Y := by
    rintro _ ⟨_, ⟨t, ht, h, hh, rfl⟩, rfl⟩
    exact ⟨_, hcomap _ (liftQuotient_comp_evalAlgHom_mul T H ht hh)⟩
  have hYK (y : GL n k) (hy : toPrimeSpectrum y ∈ Y) : y ∈ K := by
    obtain ⟨q, hq⟩ := hy
    obtain ⟨M, hM, hqM⟩ := q.asIdeal.exists_le_maximal q.2.ne_top
    obtain ⟨χ, hχM⟩ := exists_algHom_ker_eq_of_isMaximal k B M
    obtain ⟨t, ht, h, hh, hth⟩ := exists_comp_evalAlgHom_mul_eq T H χ
    have hle : (toPrimeSpectrum y).asIdeal ≤ (toPrimeSpectrum (t * h)).asIdeal := by
      rw [← hq, ← hcomap χ hth]
      exact Ideal.comap_mono (hχM ▸ hqM)
    have hmax : (toPrimeSpectrum y).asIdeal.IsMaximal :=
      RingHom.ker_isMaximal_of_surjective _ fun c ↦ ⟨algebraMap k _ c, by simp⟩
    rw [toPrimeSpectrum_injective (PrimeSpectrum.ext
      (hmax.eq_of_le (PrimeSpectrum.isPrime _).ne_top hle))]
    exact ⟨t, ht, h, hh, rfl⟩
  have hYcl : Y ⊆ closure (toPrimeSpectrum '' (K : Set (GL n k))) := by
    rintro _ ⟨q, rfl⟩
    have hq : q ∈ closure (closedPoints (PrimeSpectrum B)) := by
      rw [closure_closedPoints]
      trivial
    refine closure_mono ?_ (image_closure_subset_closure_image (PrimeSpectrum.continuous_comap _)
      ⟨q, hq, rfl⟩)
    rintro _ ⟨q, hq, rfl⟩
    have := (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).1 hq
    obtain ⟨χ, hχq⟩ := exists_algHom_ker_eq_of_isMaximal k B q.asIdeal
    obtain ⟨t, ht, h, hh, hth⟩ := exists_comp_evalAlgHom_mul_eq T H χ
    obtain rfl : q = ⟨RingHom.ker χ, RingHom.ker_isPrime _⟩ := PrimeSpectrum.ext hχq.symm
    exact ⟨t * h, ⟨t, ht, h, hh, rfl⟩, (hcomap χ hth).symm⟩
  have hYc : IsConstructible Y := by
    change IsConstructible (Set.range _)
    rw [← Set.image_univ]
    refine PrimeSpectrum.isConstructible_comap_image ?_ .univ
    refine RingHom.FinitePresentation.of_finiteType.1 ?_
    refine RingHom.FiniteType.of_comp_finiteType (f := algebraMap k (CoordinateRing n k)) ?_
    rw [AlgHom.comp_algebraMap]
    exact RingHom.finiteType_algebraMap.2 inferInstance
  have hcl_eq : closure (toPrimeSpectrum '' (K : Set (GL n k))) =
      PrimeSpectrum.zeroLocus (G : Set (CoordinateRing n k)) := by
    rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, ← hJK]
    congr 1
    ext a
    simp only [PrimeSpectrum.mem_vanishingIdeal, Set.mem_image, SetLike.mem_coe,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, JK, mem_vanishingIdeal]
    rfl
  refine mem_of_mem_closure_of_isConstructible hYc hYK
    ((closure_minimal hYcl isClosed_closure).antisymm (closure_mono hKY)) ?_ ?_
  · rw [hcl_eq]
    exact (PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical G hGp.isRadical).2 hGp
  · rw [hcl_eq]
    exact hg

end Product

/-! ### The central–geometric product for closed subgroup schemes -/

section Scheme

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

variable {I J : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k] [J.IsHopfIdeal k]

/-- If the closed subgroup scheme `V(J) ⊆ V(I)` contains the commutators of `V(I)`, then the
commutators of `R`-points of `V(I)` are `R`-points of `V(J)`. -/
theorem commutatorElement_mem_zeroLocus (h : I ≤ J)
    [IsMonHom.ContainsCommutators (subgroupSchemeHom h)] {R : Type u} [CommRing R] [Algebra k R]
    {g g' : GL n R} (hg : g ∈ zeroLocus I R) (hg' : g' ∈ zeroLocus I R) :
    ⁅g, g'⁆ ∈ zeroLocus J R := by
  obtain ⟨c, hc⟩ := IsMonHom.ContainsCommutators.exists_comp_eq_commutator (subgroupSchemeHom h)
    (zeroLocusMulEquiv I R ⟨g, hg⟩) (zeroLocusMulEquiv I R ⟨g', hg'⟩)
  set c' := (zeroLocusMulEquiv J R).symm c
  have key : zeroLocusMulEquiv I R ⟨c', zeroLocus_anti h c'.2⟩ =
      zeroLocusMulEquiv I R ⁅(⟨g, hg⟩ : zeroLocus I R), ⟨g', hg'⟩⁆ := by
    rw [← zeroLocusMulEquiv_comp_subgroupSchemeHom h, MulEquiv.apply_symm_apply, hc,
      map_commutatorElement, commutatorElement_def]
  have := congrArg Subtype.val ((zeroLocusMulEquiv I R).injective key)
  rw [show ⁅g, g'⁆ = (c' : GL n R) from this.symm]
  exact c'.2

/-- The standard representation of the `k`-points of `V(I)` is semisimple if and only if the
matrix group `zeroLocus I k` acts semisimply on `kⁿ`: they have the same stable subspaces. -/
theorem isSemisimpleRepresentation_standardRepresentation_iff (I : Ideal (CoordinateRing n k))
    [I.IsHopfIdeal k] :
    Representation.IsSemisimpleRepresentation (standardRepresentation I) ↔
      Representation.IsSemisimpleRepresentation
        ((toRepresentation n k).comp (zeroLocus I k).subtype) := by
  have hpt (g : points (subgroupScheme I) k) (v : n → k) :
      standardRepresentation I g v =
        (((zeroLocusMulEquiv I k).symm g : GL n k) : Matrix n n k) *ᵥ v := by
    rw [standardRepresentation, RationalHom.representation_apply, RationalHom.points_apply,
      Matrix.toLin'_apply]
    congr 3
    conv_lhs => rw [← (zeroLocusMulEquiv I k).apply_symm_apply g]
    exact homMulEquiv_zeroLocusMulEquiv_comp _
  refine (Subrepresentation.orderIsoOfForallIff fun U ↦ ⟨fun h g v hv ↦ ?_,
    fun h g v hv ↦ ?_⟩).complementedLattice_iff
  · have := h (zeroLocusMulEquiv I k g) v hv
    rwa [hpt, MulEquiv.symm_apply_apply] at this
  · rw [hpt]
    exact h _ v hv

variable [IsAlgClosed k] [CharZero k]

/-- The central–geometric product on `k`-points: every point of `G°` is a product `t h` of a point
`t` of `Z(G°)°` and a point `h` of `H°`. This is `exists_mul_eq_of_commutator_mem` for the matrices
of the points. (blueprint: `lemma-identity-component`) -/
theorem exists_mul_eq_of_containsCommutators (h : I ≤ J)
    [IsMonHom.ContainsCommutators (subgroupSchemeHom h)]
    [Representation.IsSemisimpleRepresentation (standardRepresentation (identityComponent I))]
    (g : points (subgroupScheme (identityComponent I)) k) :
    ∃ (t : points (subgroupScheme (identityComponent (center (identityComponent I)))) k)
      (x : points (subgroupScheme (identityComponent J)) k),
      t ≫ subgroupSchemeHom ((le_center _).trans (le_identityComponent _)) *
        x ≫ subgroupSchemeHom (identityComponent_mono I h) = g := by
  have := (isSemisimpleRepresentation_standardRepresentation_iff _).1 ‹_›
  set g' := (zeroLocusMulEquiv (identityComponent I) k).symm g
  obtain ⟨t, ht, x, hx, htx⟩ := exists_mul_eq_of_commutator_mem h
    (fun a ha b hb ↦ commutatorElement_mem_zeroLocus h ha hb) g'.2
  refine ⟨zeroLocusMulEquiv _ k ⟨t, ht⟩, zeroLocusMulEquiv _ k ⟨x, hx⟩, ?_⟩
  rw [zeroLocusMulEquiv_comp_subgroupSchemeHom, zeroLocusMulEquiv_comp_subgroupSchemeHom, ← map_mul,
    ← (zeroLocusMulEquiv (identityComponent I) k).apply_symm_apply g]
  congr 1
  exact Subtype.ext htx

/-- **The central–geometric product.** Let `H = V(J) ⊆ G = V(I)` be closed subgroups of `GL_n` over
an algebraically closed field of characteristic zero such that `H` contains the commutators of `G`
and `G°` acts semisimply on `kⁿ`. Then `G° = Z(G°)° H°`: the multiplication morphism
`Z(G°)° × H° ⟶ G°` is surjective.

Its image contains the closed points of `G°`, which are `k`-points
(`exists_mul_eq_of_containsCommutators`), and it is constructible (Chevalley); a constructible
subset of the Jacobson space `G°` containing all its closed points is everything.
(blueprint: `lemma-identity-component`) -/
theorem surjective_mulCenterIdentityComponent (h : I ≤ J)
    [IsMonHom.ContainsCommutators (subgroupSchemeHom h)]
    [Representation.IsSemisimpleRepresentation (standardRepresentation (identityComponent I))] :
    Function.Surjective (mulCenterIdentityComponent h).left.base := by
  set G := subgroupScheme (identityComponent I)
  have : IsNoetherianRing (CoordinateRing n k ⧸ identityComponent I) :=
    Algebra.FiniteType.isNoetherianRing k _
  have : IsNoetherian G.left :=
    inferInstanceAs (IsNoetherian (Spec (.of (CoordinateRing n k ⧸ identityComponent I))))
  have : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace G.hom
  -- the image contains the closed points
  let X := (Spec (.of k)).asOver (Spec (.of k))
  let e : X ≅ 𝟙_ (Over (Spec (.of k))) := Over.isoMk (Iso.refl (Spec (.of k))) (by
    simp [X, specOverSpec_over, Algebra.algebraMap_self])
  have hclosed (y : G.left) (hy : IsClosed {y}) :
      y ∈ Set.range (mulCenterIdentityComponent h).left.base := by
    set s := GrpObj.sectionOfIsClosed G y hy
    obtain ⟨t, x, htx⟩ := exists_mul_eq_of_containsCommutators h (e.hom ≫ s)
    have hs : (e.inv ≫ lift t x) ≫ mulCenterIdentityComponent h = s := by
      unfold mulCenterIdentityComponent
      rw [Category.assoc, ← Category.assoc (lift t x), lift_map,
        ← Hom.mul_def, htx, ← Category.assoc, e.inv_hom_id, Category.id_comp]
    obtain ⟨a⟩ : Nonempty (Spec (.of k)) := inferInstance
    refine ⟨(e.inv ≫ lift t x).left a, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hs, GrpObj.sectionOfIsClosed_left_apply]
  -- the image is constructible
  set f := mulCenterIdentityComponent h
  have : LocallyOfFiniteType f.left := by
    have : LocallyOfFiniteType (f.left ≫ G.hom) := by rw [Over.w f]; infer_instance
    exact locallyOfFiniteType_of_comp f.left G.hom
  have : QuasiCompact (subgroupScheme (identityComponent (center (identityComponent I))) ⊗
      subgroupScheme (identityComponent J)).hom := by
    rw [Over.tensorObj_hom]
    infer_instance
  have : CompactSpace (subgroupScheme (identityComponent (center (identityComponent I))) ⊗
      subgroupScheme (identityComponent J)).left :=
    QuasiCompact.compactSpace_of_compactSpace (Over.hom _)
  have : QuasiCompact f.left := quasiCompact_of_compactSpace _
  have hc : IsConstructible (Set.range f.left.base) := by
    rw [← Set.image_univ]
    exact f.left.isConstructible_image .univ
  intro y
  by_contra hy
  replace hy : y ∈ (Set.range f.left.base)ᶜ := hy
  obtain ⟨u, hu, hne, hsub⟩ := exists_isOpen_inter_closure_subset_of_isConstructible
    hc.compl ⟨y, hy⟩
  obtain ⟨z, ⟨hzu, hzcl⟩, hz⟩ := nonempty_inter_closedPoints hne
    (hu.isLocallyClosed.inter isClosed_closure.isLocallyClosed)
  exact hsub ⟨hzu, hzcl⟩ (hclosed z hz)

end Scheme

end AlgebraicGeometry.GeneralLinearGroup
