import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Torus.SplitMono
import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # Torus complements of a kernel with split torus quotient

Let `q : R ⟶ D` be a homomorphism whose actual scheme kernel has the same points as a subgroup
`u : U ⟶ R` on every test scheme, and let `s : L ⟶ R` be a monomorphism. If `s` and `u` meet
trivially on every test scheme, then `s ≫ q` is a monomorphism. If `s ≫ q` is an isomorphism,
the multiplication `L ×_S U ⟶ R`, `(l, v) ↦ s(l) u(v)`, is an isomorphism of schemes.

Over an infinite field, a monomorphism of split tori that is surjective on rational points is an
isomorphism: a nonzero integer relation among the rows of its character matrix would give a
nontrivial character of the target that is trivial on the image of rational points. Combining
the two parts gives the scheme-level splitting `R ≅ L ×_S U` of Milne 2017, Theorem 16.33(d),
from a split torus quotient with kernel `U`, trivial intersection, and rational surjectivity.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-! ### Rank comparison for split tori -/

namespace splitTorus

variable {k : Type u} [Field k] {I J : Type u} [Finite I] [Finite J]

local notation "𝕊" => Spec (CommRingCat.of k)

omit [Finite I] in
private theorem prod_zpow_eq_zpow_sum {G : Type*} [CommGroup G] (s : Finset I) (f : I → ℤ)
    (a : G) : ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add]

omit [Finite I] [Finite J] in
/-- An infinite field has, for every nonzero integer `m`, a unit whose `m`-th power is not `1`. -/
theorem exists_units_zpow_ne_one [Infinite k] {m : ℤ} (hm : m ≠ 0) : ∃ a : kˣ, a ^ m ≠ 1 := by
  classical
  obtain ⟨a, ha⟩ :=
    Infinite.exists_notMem_finset (insert (0 : k) (Polynomial.nthRoots m.natAbs (1 : k)).toFinset)
  rw [Finset.mem_insert, not_or, Multiset.mem_toFinset,
    Polynomial.mem_nthRoots (Int.natAbs_pos.mpr hm)] at ha
  refine ⟨Units.mk0 a ha.1, fun h => ha.2 ?_⟩
  have h' := (pow_natAbs_eq_one (a := Units.mk0 a ha.1) (n := m)).mpr h
  have h'' := congrArg Units.val h'
  simpa using h''

/-- The coordinates of the row combination `∑ⱼ nⱼ • mⱼ`. -/
theorem characterRows_apply [Fintype J] (f : splitTorus 𝕊 I ⟶ splitTorus 𝕊 J) (n : J → ℤ)
    (i : I) : characterRows f n i = ∑ j, n j * characterMatrix f j i := by
  classical
  obtain rfl : Fintype.ofFinite J = ‹Fintype J› := Subsingleton.elim _ _
  simp only [characterRows, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]

/-- Over an infinite field, if a homomorphism of split tori is surjective on rational points,
the rows of its integer matrix are linearly independent over `ℤ`. -/
theorem characterRows_injective_of_rationalPoints_surjective [Infinite k]
    (f : splitTorus 𝕊 I ⟶ splitTorus 𝕊 J) (hf : Function.Surjective (rationalPoints.map f)) :
    Function.Injective (characterRows f) := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  let _ : Fintype J := Fintype.ofFinite J
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro n hn
  rw [LinearMap.mem_ker] at hn
  by_contra hne
  obtain ⟨j₀, hj₀⟩ : ∃ j, n j ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  obtain ⟨a, ha⟩ := exists_units_zpow_ne_one (k := k) hj₀
  let g : 𝕊 ⟶ 𝕊 := 𝟙 _
  obtain ⟨x, hx⟩ := hf ((affinePointsEquiv J g).symm (Pi.mulSingle j₀ a))
  rw [rationalPoints.map_apply] at hx
  apply ha
  have key : ∏ j, affinePointsEquiv J g (x ≫ f.hom.hom) j ^ n j = 1 := by
    simp_rw [affinePointsEquiv_comp]
    calc ∏ j, (∏ i, affinePointsEquiv I g x i ^ characterMatrix f j i) ^ n j
        = ∏ j, ∏ i, affinePointsEquiv I g x i ^ (n j * characterMatrix f j i) := by
          refine Finset.prod_congr rfl fun j _ => ?_
          rw [← Finset.prod_zpow]
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [← zpow_mul, mul_comm]
      _ = ∏ i, ∏ j, affinePointsEquiv I g x i ^ (n j * characterMatrix f j i) :=
          Finset.prod_comm
      _ = ∏ i, affinePointsEquiv I g x i ^ characterRows f n i := by
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [prod_zpow_eq_zpow_sum, characterRows_apply]
      _ = 1 := by
          rw [hn]
          simp
  rw [hx, MulEquiv.apply_symm_apply] at key
  rw [Finset.prod_eq_single j₀ (fun j _ hj => by rw [Pi.mulSingle_eq_of_ne hj, one_zpow])
    (fun h => absurd (Finset.mem_univ j₀) h), Pi.mulSingle_eq_same] at key
  exact key

/-- Over an infinite field, a homomorphism `𝔾_m^I ⟶ 𝔾_m^J` that is surjective on rational
points has `Nat.card J ≤ Nat.card I`. -/
theorem card_le_of_rationalPoints_surjective [Infinite k] (f : splitTorus 𝕊 I ⟶ splitTorus 𝕊 J)
    (hf : Function.Surjective (rationalPoints.map f)) : Nat.card J ≤ Nat.card I := by
  let _ : Fintype I := Fintype.ofFinite I
  let _ : Fintype J := Fintype.ofFinite J
  have h := LinearMap.finrank_le_finrank_of_injective
    (characterRows_injective_of_rationalPoints_surjective f hf)
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at h
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact h

end splitTorus

section SplitTorus

variable {k : Type u} [Field k] {H K : GroupScheme (Spec (CommRingCat.of k))}

/-- Over an infinite field, a monomorphism of split tori that is surjective on rational points is
an isomorphism of group schemes. -/
theorem IsSplitTorus.isIso_of_mono_of_rationalPoints_surjective [Infinite k]
    (hH : IsSplitTorus H) (hK : IsSplitTorus K) (f : H ⟶ K) (hf : Mono f.hom.hom)
    (hs : Function.Surjective (rationalPoints.map f)) : IsIso f := by
  obtain ⟨I, _, ⟨eH⟩⟩ := hH
  obtain ⟨J, _, ⟨eK⟩⟩ := hK
  refine splitTorus.isIso_of_mono_of_iso eH eK f hf
    (splitTorus.card_le_of_rationalPoints_surjective (eH.inv ≫ f ≫ eK.hom) fun y => ?_)
  obtain ⟨x, hx⟩ := hs (y ≫ eK.inv.hom.hom)
  refine ⟨x ≫ eH.hom.hom.hom, ?_⟩
  rw [rationalPoints.map_apply] at hx ⊢
  have h1 : eH.hom.hom.hom ≫ (eH.inv ≫ f ≫ eK.hom).hom.hom = f.hom.hom ≫ eK.hom.hom.hom := by
    rw [← Grp.comp_hom_hom, Iso.hom_inv_id_assoc, Grp.comp_hom_hom]
  rw [Category.assoc, h1, ← Category.assoc, hx, Category.assoc, ← Grp.comp_hom_hom,
    Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]

end SplitTorus

/-! ### The complement of a kernel -/

section Complement

variable {S : Scheme.{u}} {L U R D : GroupScheme S} (s : L ⟶ R) (u : U ⟶ R) (q : R ⟶ D)

/-- Evaluation of the subgroup multiplication morphism on an arbitrary point of the product. -/
theorem comp_subgroupMultiplication_eq {T : Over S} (w : T ⟶ L.X ⊗ U.X) :
    w ≫ subgroupMultiplication s u =
      (w ≫ fst L.X U.X ≫ s.hom.hom) * (w ≫ snd L.X U.X ≫ u.hom.hom) := by
  rw [subgroupMultiplication, MonObj.comp_mul]

variable {s u q}

/-- If the scheme kernel of `q` has the points of `u`, then `u ≫ q` is trivial on points. -/
theorem comp_quotient_eq_one (hq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range u)
    {T : Over S} (y : T ⟶ U.X) : y ≫ u.hom.hom ≫ q.hom.hom = 1 := by
  have hy : y ≫ u.hom.hom ∈ (SubgroupFunctor.range (kernelι q)).carrier T := by
    rw [hq]
    exact ⟨y, rfl⟩
  rw [← Category.assoc]
  exact (mem_range_kernelι_iff q _).mp hy

/-- A subgroup meeting the kernel of `q` trivially on every test maps monomorphically by `q`. -/
theorem mono_comp_of_inf_eq_bot (hs : Mono s.hom.hom)
    (hq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range u)
    (hint : SubgroupFunctor.range s ⊓ SubgroupFunctor.range u = ⊥) :
    Mono (s ≫ q).hom.hom := by
  constructor
  intro T x y hxy
  rw [Grp.comp_hom_hom] at hxy
  have hk : (x / y) ≫ s.hom.hom ∈ (SubgroupFunctor.range (kernelι q)).carrier T := by
    rw [mem_range_kernelι_iff, Category.assoc, GrpObj.div_comp, hxy, div_self']
  have hb : (x / y) ≫ s.hom.hom ∈
      (SubgroupFunctor.range s ⊓ SubgroupFunctor.range u).carrier T := by
    rw [SubgroupFunctor.inf_carrier, Subgroup.mem_inf]
    exact ⟨⟨x / y, rfl⟩, hq ▸ hk⟩
  rw [hint, SubgroupFunctor.bot_carrier, Subgroup.mem_bot, GrpObj.div_comp, div_eq_one] at hb
  exact (cancel_mono s.hom.hom).mp hb

/-- If `s ≫ q` is an isomorphism and the scheme kernel of `q` has the points of the
monomorphism `u`, then multiplication `L ×_S U ⟶ R` is an isomorphism of schemes. -/
theorem isIso_subgroupMultiplication_of_isIso_comp (hu : Mono u.hom.hom)
    (hq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range u) [IsIso (s ≫ q)] :
    IsIso (subgroupMultiplication s u) := by
  have hsq : IsIso (s ≫ q).hom.hom := (inferInstance : IsIso ((Grp.forget _).map (s ≫ q)))
  refine isIso_of_yoneda_map_bijective _ fun T => ⟨fun w w' h => ?_, fun x => ?_⟩
  · simp only at h
    rw [comp_subgroupMultiplication_eq, comp_subgroupMultiplication_eq] at h
    have hq' := congrArg (· ≫ q.hom.hom) h
    simp only [MonObj.mul_comp, Category.assoc, comp_quotient_eq_one hq, MonObj.comp_one,
      mul_one] at hq'
    have ha : w ≫ fst L.X U.X = w' ≫ fst L.X U.X := by
      apply (cancel_mono (s ≫ q).hom.hom).mp
      rw [Grp.comp_hom_hom, Category.assoc, Category.assoc]
      exact hq'
    have h' : (w ≫ fst L.X U.X ≫ s.hom.hom) * (w ≫ snd L.X U.X ≫ u.hom.hom) =
        (w ≫ fst L.X U.X ≫ s.hom.hom) * (w' ≫ snd L.X U.X ≫ u.hom.hom) := by
      rw [h, ← Category.assoc w, ha, Category.assoc]
    have hb : w ≫ snd L.X U.X = w' ≫ snd L.X U.X :=
      (cancel_mono u.hom.hom).mp (by simpa only [Category.assoc] using mul_left_cancel h')
    exact CartesianMonoidalCategory.hom_ext _ _ ha hb
  · let a : T ⟶ L.X := x ≫ q.hom.hom ≫ (inv (s ≫ q)).hom.hom
    have ha : a ≫ s.hom.hom ≫ q.hom.hom = x ≫ q.hom.hom := by
      simp only [a, Category.assoc]
      rw [← Grp.comp_hom_hom, ← Grp.comp_hom_hom, IsIso.inv_hom_id, Grp.id_hom_hom,
        Category.comp_id]
    have hc : (a ≫ s.hom.hom)⁻¹ * x ∈ (SubgroupFunctor.range (kernelι q)).carrier T := by
      rw [mem_range_kernelι_iff, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, ha,
        inv_mul_cancel]
    rw [hq] at hc
    obtain ⟨b, hb⟩ := (SubgroupFunctor.mem_range).mp hc
    refine ⟨lift a b, ?_⟩
    simp only
    rw [comp_subgroupMultiplication_eq, lift_fst_assoc, lift_snd_assoc, hb, mul_inv_cancel_left]

variable (s) in
/-- The scheme isomorphism `L ×_S U ≅ R`, `(l, v) ↦ s(l) u(v)`, of
`isIso_subgroupMultiplication_of_isIso_comp`. -/
def kernelComplementIso (hu : Mono u.hom.hom)
    (hq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range u) [IsIso (s ≫ q)] :
    L.X ⊗ U.X ≅ R.X :=
  haveI : IsIso (subgroupMultiplication s u) := isIso_subgroupMultiplication_of_isIso_comp hu hq
  asIso (subgroupMultiplication s u)

variable (s) in
@[simp]
theorem kernelComplementIso_hom (hu : Mono u.hom.hom)
    (hq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range u) [IsIso (s ≫ q)] :
    (kernelComplementIso s hu hq).hom = subgroupMultiplication s u := rfl

/-- Over an infinite field, let `q : R ⟶ D` be a homomorphism to a split torus whose scheme
kernel has the points of a monomorphism `u : U ⟶ R`, and let `s : L ⟶ R` be a monomorphism from
a split torus meeting `u` trivially on every test scheme. If `s ≫ q` is surjective on rational
points, multiplication `L ×_S U ⟶ R` is an isomorphism of schemes. -/
theorem isIso_subgroupMultiplication_of_splitTorus_quotient {k : Type u} [Field k] [Infinite k]
    {L U R D : GroupScheme (Spec (CommRingCat.of k))} {s : L ⟶ R} {u : U ⟶ R} {q : R ⟶ D}
    (hL : IsSplitTorus L) (hD : IsSplitTorus D) (hs : Mono s.hom.hom) (hu : Mono u.hom.hom)
    (hq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range u)
    (hint : SubgroupFunctor.range s ⊓ SubgroupFunctor.range u = ⊥)
    (hsurj : Function.Surjective (rationalPoints.map (s ≫ q))) :
    IsIso (subgroupMultiplication s u) := by
  have := hL.isIso_of_mono_of_rationalPoints_surjective hD (s ≫ q)
    (mono_comp_of_inf_eq_bot hs hq hint) hsurj
  exact isIso_subgroupMultiplication_of_isIso_comp hu hq

/-- If every rational point of `R` is a product of a rational point of `u` and one of `s`, and
`q` is surjective on rational points, then `s ≫ q` is surjective on rational points. -/
theorem rationalPoints_surjective_comp_of_factorization {k : Type u} [CommRing k]
    {L U R D : GroupScheme (Spec (CommRingCat.of k))} {s : L ⟶ R} {u : U ⟶ R} {q : R ⟶ D}
    (hq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range u)
    (hfac : ∀ b : rationalPoints R, ∃ (v : rationalPoints U) (t : rationalPoints L),
      (v ≫ u.hom.hom) * (t ≫ s.hom.hom) = b)
    (hqs : Function.Surjective (rationalPoints.map q)) :
    Function.Surjective (rationalPoints.map (s ≫ q)) := by
  intro d
  obtain ⟨b, rfl⟩ := hqs d
  obtain ⟨v, t, rfl⟩ := hfac b
  refine ⟨t, ?_⟩
  rw [rationalPoints.map_apply, rationalPoints.map_apply, MonObj.mul_comp, Category.assoc,
    Category.assoc, comp_quotient_eq_one hq, one_mul, Grp.comp_hom_hom]

end Complement

end Langlands.GroupScheme
