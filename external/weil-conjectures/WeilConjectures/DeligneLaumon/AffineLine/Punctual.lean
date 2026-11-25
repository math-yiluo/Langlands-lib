/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.Defs
public import WeilConjectures.WeilSheaf.SupportUpperStar
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseDenseOpen
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius.Irreducible

/-!
# Punctual Weil sheaves on the affine line

A Weil sheaf on the affine line is *punctual* if its support, a set of closed points, is finite.
The direct image `j_*M` of a lisse Weil sheaf on a dense open has no nonzero punctual subsheaf:
every morphism from a punctual sheaf to it vanishes
(`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.eq_zero_of_support_finite`). This is Step 0 of
the description of the perverse t-structure on a smooth curve (blueprint
`lemma-perverse-sheaves-curve`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- The affine line has two distinct points: the generic point and a closed point, the
polynomial ring `k₀[x]` not being a field. -/
instance _root_.AlgebraicGeometry.affineLine.nontrivial (k₀ : Type u) [Field k₀] :
    Nontrivial (affineLine k₀) := by
  let e := AffineSpace.SpecIso PUnit.{u + 1} (CommRingCat.of k₀)
  let R := MvPolynomial PUnit.{u + 1} (CommRingCat.of k₀)
  have hR : ¬ IsField R := fun h ↦ Polynomial.not_isField (R := k₀)
    (MulEquiv.isField h (MvPolynomial.uniqueAlgEquiv k₀ PUnit.{u + 1}).symm.toMulEquiv)
  obtain ⟨I, hI1, hI2⟩ := (Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top).1 hR
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI2.ne
  let p : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  let q : PrimeSpectrum R := ⟨M, hM.isPrime⟩
  have hpq : p ≠ q := fun h ↦
    hI1.ne' (le_bot_iff.1 (hIM.trans (congrArg PrimeSpectrum.asIdeal h).symm.le))
  exact ⟨⟨e.inv.base p, e.inv.base q, fun h ↦ hpq (e.inv.isOpenEmbedding.injective h)⟩⟩

open scoped ProEtale in
/-- **A middle extension has no punctual subsheaf**: every morphism from a Weil sheaf `G` of
finite support on the affine line to the direct image `j_*M` of a lisse Weil sheaf on a dense
open vanishes. Let `V₀` be the complement of the support of `G`; then `G|_{V₀} = 0`, its stalks
at the closed points of `V₀` vanishing. The adjoint `j̄^* G ⟶ M` of the morphism therefore
vanishes on `Ū ∩ V̄₀`, and every point of `Ū` specializes from a point of `Ū ∩ V̄₀`, namely from
the generic point of the irreducible geometric line, which lies over `V₀` since the affine line
is not a single closed point. A morphism into the lisse `M` vanishing there vanishes
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.eq_zero_of_adicUpperStar_map_eq_zero`).
(blueprint: `lemma-perverse-sheaves-curve`, Step 0) -/
theorem LisseOnDenseOpen.eq_zero_of_support_finite (D : LisseOnDenseOpen k₀ l)
    {G : WeilSheaf k₀ l (affineLine k₀)} (hG : G.support.Finite) (i : G ⟶ D.directImage) :
    i = 0 := by
  classical
  set S : Set (affineLine k₀) := ⋃ x ∈ G.support, {x.1} with hS
  have hSc : IsClosed S :=
    hG.isClosed_biUnion fun x _ ↦ (affineLine k₀).isClosed_singleton_of_mem_finitePoints x.2
  let V₀ : (affineLine k₀).Opens := ⟨Sᶜ, hSc.isOpen_compl⟩
  -- `G` vanishes on `V₀`
  have hz : IsZero ((upperStar V₀.ι).obj G) := by
    refine isZero_upperStar_of_forall_notMem_support V₀.ι G fun y hy ↦ ?_
    have hV : V₀.ι.base y.1 ∈ (V₀ : Set (affineLine k₀)) := by
      rw [Scheme.Opens.ι_apply]
      exact y.1.2
    exact hV (Set.mem_biUnion hy rfl)
  set jb := Scheme.Hom.geometricFiberMap D.j (comp_over D.j (Spec (CommRingCat.of k₀)))
  set gb := Scheme.Hom.geometricFiberMap V₀.ι (comp_over V₀.ι (Spec (CommRingCat.of k₀)))
  set prA := (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj
  have : IrreducibleSpace (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
    Scheme.Hom.irreducibleSpace_geometricFiber _
  -- the generic point of the geometric line lies over `V₀`
  have hξ : prA.base (genericPoint _) ∈ (V₀ : Set (affineLine k₀)) := by
    intro hS
    obtain ⟨x, -, hxe⟩ := Set.mem_iUnion₂.1 hS
    have hcl := (affineLine k₀).isClosed_singleton_of_mem_finitePoints x.2
    rw [Set.mem_singleton_iff] at hxe
    obtain ⟨a, b, hab⟩ := affineLine.nontrivial k₀
    have key (z : affineLine k₀) : z = x.1 := by
      obtain ⟨z', hz'⟩ :=
        Scheme.Hom.geometricFiberProj_surjective (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) z
      have h1 := ((genericPoint_spec _).specializes (Set.mem_univ z')).map prA.continuous
      rw [hz', hxe] at h1
      exact h1.mem_closed hcl rfl
    exact hab ((key a).trans (key b).symm)
  -- every point of `Ū` specializes from a point of `Ū ∩ V̄₀`
  have hgen : ∀ y, ∃ p : (Limits.pullback jb gb : Scheme.{u}),
      (pullback.fst jb gb).base p ⤳ y := by
    intro y
    have h1 := (genericPoint_spec
      ((affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber)).specializes
        (Set.mem_univ (jb.base y))
    obtain ⟨η, hη⟩ : genericPoint _ ∈ Set.range jb.base :=
      h1.mem_open jb.isOpenEmbedding.isOpen_range ⟨y, rfl⟩
    obtain ⟨v, hv1, -⟩ := Scheme.exists_preimage_of_isPullback
      (Scheme.Hom.isPullback_geometricFiberMap V₀.ι (comp_over V₀.ι _))
      (genericPoint _) ⟨_, hξ⟩ (by rw [Scheme.Opens.ι_apply])
    obtain ⟨p, hp1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := jb) (g := gb) η v
      (hη.trans hv1.symm)
    refine ⟨p, ?_⟩
    rw [hp1]
    rw [← hη] at h1
    exact jb.isOpenEmbedding.isInducing.specializes_iff.1 h1
  -- the adjoint morphism `j̄^* G ⟶ M` vanishes
  have hcar : IsZero ((gb)^*ᵃ[l].obj G.obj.carrier) := isZero_iff_isZero_carrier.1 hz
  let adj := ProEtale.adicUpperStarLowerStarAdjunction l jb
  let φ := (adj.homEquiv _ _).symm i.hom.hom.f
  have hφ : (pullback.fst jb gb)^*ᵃ[l].map φ = 0 :=
    ((Functor.map_isZero ((pullback.snd jb gb)^*ᵃ[l]) hcar).of_iso
      ((ProEtale.adicUpperStarCompIso l (pullback.condition (f := jb) (g := gb))).app
        G.obj.carrier)).eq_of_src _ _
  have hφ0 : φ = 0 :=
    ProEtale.IsAdicLisseSheaf.eq_zero_of_adicUpperStar_map_eq_zero _ hgen D.lisse φ hφ
  have hf : i.hom.hom.f = 0 := by
    rw [← (adj.homEquiv _ _).apply_symm_apply i.hom.hom.f]
    change adj.homEquiv _ _ φ = 0
    rw [hφ0, Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
  exact ObjectProperty.hom_ext _ <| ObjectProperty.hom_ext _ <| Endofunctor.Algebra.Hom.ext hf

end WeilSheaf

end AlgebraicGeometry
