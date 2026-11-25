/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import WeilConjectures.CategoryTheory.CartanEilenbergComparisonColumnStep

/-! # Augmented comparison of Cartan–Eilenberg resolutions

Source: Stacks Project, Tags 015H, 015I and 015K
(blueprint: lem-weil-pbc-ce-augmented-comparison).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- An exact additive functor admits an augmented bicomplex comparison.
This statement concerns the comparison itself; it does not form total complexes.
Source: Stacks Project, Tags 015H, 015I and 015K
(blueprint: lem-weil-pbc-ce-augmented-comparison).

Proof: in every complex degree p use the exact sequences
0 → Bᵖ → Zᵖ → Hᵖ → 0 and 0 → Zᵖ → Kᵖ → Bᵖ⁺¹ → 0, and their
resolution-column analogues. Exactness of F preserves these sequences and the
augmented column exactness. For the target, the stated injectivity conditions
make the boundary, cycle, cohomology and original columns injective resolutions;
the sequences are degreewise short exact by abelian homology theory.
Choose a common lower bound for I and J. Below that bound all boundary columns
are zero. Induct on p starting with the zero map on the lowest boundary column.
Given its comparison map, lift the cohomology augmentation map through the source
augmentation into the target injective cohomology column by the lifting property
of monomorphic quasi-isomorphisms against bounded-below injective complexes
(lem-weil-pbc-lift-along-injective-quasi-iso, Stacks Tag 013P(2)). Apply
exists_horseshoe_morphism_lift_exact_source to the boundary/cycle/cohomology
sequence to get a cycle comparison compatible with both endpoint maps.
Lift the next boundary augmentation map by the same lifting property. Apply
the exact-source horseshoe lift to the cycle/original/next-boundary sequence
with these chosen endpoint maps to obtain the original column comparison.
Retain the next-boundary map for the next induction step, choosing each map
only once. The horizontal differential factors through the next-boundary and
next-cycle columns. The endpoint equations from the two horseshoe lifts make
the original column comparisons commute with this factorization. Each is already
a chain map in the resolution degree. They therefore assemble into a bicomplex
map. Their degree-zero augmentation equations are exactly the displayed identity,
using singleObjXSelf to identify the source single-degree components. -/
theorem exists_cartanEilenberg_augmented_comparison
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Abelian A] [Abelian B] (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (u : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ L)
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (eI : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ I)
    (hIbelow : ∃ i : ℤ, ∀ p : ℤ, p < i → IsZero (I.X p))
    (hIcol : ∀ p : ℤ, QuasiIso (eI.f p))
    (hIres : ∀ p : ℤ,
      QuasiIso (HomologicalComplex.cyclesMap eI p) ∧
      QuasiIso (image.map (Arrow.homMk' (eI.f (p - 1)) (eI.f p) (eI.comm (p - 1) p))) ∧
      QuasiIso (HomologicalComplex.homologyMap eI p))
    (J : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (eJ : ((CochainComplex.single₀ B).mapHomologicalComplex (ComplexShape.up ℤ)).obj L ⟶ J)
    (hJbelow : ∃ i : ℤ, ∀ p : ℤ, p < i → IsZero (J.X p))
    (hJcol : ∀ p : ℤ, QuasiIso (eJ.f p))
    (hJinj : ∀ (p : ℤ) (q : ℕ), Injective ((J.X p).X q))
    (hJinj' : ∀ (p : ℤ) (q : ℕ),
      Injective ((J.cycles p).X q) ∧
      Injective ((image (J.d (p - 1) p)).X q) ∧
      Injective ((J.homology p).X q))
    (hJres : ∀ p : ℤ,
      QuasiIso (HomologicalComplex.cyclesMap eJ p) ∧
      QuasiIso (image.map (Arrow.homMk' (eJ.f (p - 1)) (eJ.f p) (eJ.comm (p - 1) p))) ∧
      QuasiIso (HomologicalComplex.homologyMap eJ p)) :
    let FI : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℕ) :=
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I
    ∃ φ : FI ⟶ J, ∀ p : ℤ,
      F.map ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (K.X p)).inv ≫
          (eI.f p).f 0) ≫ (φ.f p).f 0 =
        u.f p ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (L.X p)).inv ≫
          (eJ.f p).f 0 := by
  classical
  dsimp only
  let G := F.mapHomologicalComplex (ComplexShape.up ℕ)
  let aI (p : ℤ) :=
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (K.X p)).inv ≫ (eI.f p).f 0
  let aJ (p : ℤ) :=
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (L.X p)).inv ≫ (eJ.f p).f 0
  obtain ⟨iI, hiI⟩ := hIbelow
  obtain ⟨iJ, hiJ⟩ := hJbelow
  let i := min iI iJ
  have zi (p : ℤ) (hp : p < i) : IsZero (I.X p) := hiI p (by omega)
  have zj (p : ℤ) (hp : p < i) : IsZero (J.X p) := hiJ p (by omega)
  let P (n : ℕ) : ℤ := i + n
  let BI (n : ℕ) := image (I.d (P n - 1) (P n))
  let BJ (n : ℕ) := image (J.d (P n - 1) (P n))
  let Bound (n : ℕ) := {b : G.obj (BI n) ⟶ BJ n //
    F.map (aI (P n - 1) ≫ (factorThruImage (I.d (P n - 1) (P n))).f 0) ≫ b.f 0 =
      u.f (P n - 1) ≫ aJ (P n - 1) ≫
        (factorThruImage (J.d (P n - 1) (P n))).f 0}
  let Col (n : ℕ) := G.obj (I.X (P n)) ⟶ J.X (P n)
  let Good (n : ℕ) (b : Bound n) (c : Bound (n + 1)) (x : Col n) : Prop :=
    (F.map (aI (P n)) ≫ x.f 0 = u.f (P n) ≫ aJ (P n)) ∧
    (G.map (image.ι (I.d (P n - 1) (P n))) ≫ x =
      b.val ≫ image.ι (J.d (P n - 1) (P n))) ∧
    (G.map (factorThruImage (I.d (P (n + 1) - 1) (P (n + 1)))) ≫ c.val =
      eqToHom (congrArg (fun k : ℤ ↦ G.obj (I.X k)) (by dsimp only [P]; omega)) ≫ x ≫
        eqToHom (congrArg (fun k : ℤ ↦ J.X k) (by dsimp only [P]; omega)) ≫
        factorThruImage (J.d (P (n + 1) - 1) (P (n + 1))))
  have extend (n : ℕ) (b : Bound n) :
      ∃ c : Bound (n + 1), ∃ x : Col n, Good n b c x := by
    obtain ⟨x, c, hx, hc, hin, hout⟩ :=
      exists_cartanEilenberg_comparison_column_step F K L u (P n) (P (n + 1))
        (by dsimp only [P]; omega) I eI (hIcol _) (hIres _) ((hIres _).2.1)
        J eJ (hJcol _) (hJinj _) (hJinj' _) (hJres _) ((hJres _).2.1)
        (fun k ↦ (hJinj' _ k).2.1) b.val
          (by simpa only [aI, aJ, Category.assoc] using b.property)
    refine ⟨⟨c, ?_⟩, x, hx, hin, hout⟩
    simpa only [aI, aJ, Category.assoc] using hc
  let b0 : Bound 0 := ⟨0, by
    have hz : eJ.f (P 0 - 1) = 0 := (zj _ (by dsimp [P]; omega)).eq_of_tgt _ _
    simp [aJ, hz]⟩
  let transition (n : ℕ) (b : Bound n) :
      Σ c : Bound (n + 1), {x : Col n // Good n b c x} :=
    ⟨(extend n b).choose, (extend n b).choose_spec.choose,
      (extend n b).choose_spec.choose_spec⟩
  let bs : ∀ n : ℕ, Bound n := Nat.rec b0 (fun n b ↦ (transition n b).1)
  let xs (n : ℕ) : Col n := (transition n (bs n)).2.val
  have good (n : ℕ) : Good n (bs n) (bs (n + 1)) (xs n) :=
    (transition n (bs n)).2.property
  have aug (n : ℕ) : F.map (aI (P n)) ≫ (xs n).f 0 = u.f (P n) ≫ aJ (P n) :=
    (good n).1
  have comm (n : ℕ) : xs n ≫ J.d (P n) (P (n + 1)) =
      G.map (I.d (P n) (P (n + 1))) ≫ xs (n + 1) := by
    have pp : P (n + 1) - 1 = P n := by dsimp [P]; omega
    have hout := (good n).2.2
    have hin := (good (n + 1)).2.1
    have fac := congrArg (fun f ↦ f ≫ image.ι
      (J.d (P (n + 1) - 1) (P (n + 1)))) hout
    rw [Category.assoc, ← hin, ← Category.assoc, ← G.map_comp, image.fac] at fac
    simp only [Category.assoc, image.fac] at fac
    have transport (r p q : ℤ) (h : r = p)
        (x : G.obj (I.X p) ⟶ J.X p) (y : G.obj (I.X q) ⟶ J.X q)
        (hh : eqToHom (congrArg (fun k : ℤ ↦ G.obj (I.X k)) h) ≫ x ≫
          eqToHom (congrArg (fun k : ℤ ↦ J.X k) h.symm) ≫ J.d r q =
            G.map (I.d r q) ≫ y) : x ≫ J.d p q = G.map (I.d p q) ≫ y := by
      subst r
      simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using hh
    exact transport _ _ _ pp (xs n) (xs (n + 1)) fac.symm
  let φp (p : ℤ) : G.obj (I.X p) ⟶ J.X p :=
    if hp : p < i then 0 else
      eqToHom (congrArg (fun k : ℤ ↦ G.obj (I.X k)) (by dsimp only [P]; omega)) ≫
        xs (p - i).toNat ≫
        eqToHom (congrArg (fun k : ℤ ↦ J.X k) (by dsimp only [P]; omega))
  have φP (n : ℕ) : φp (P n) = xs n := by
    have h : ¬ P n < i := by dsimp [P]; omega
    have hn : (P n - i).toNat = n := by dsimp [P]; omega
    simp [φp, h, hn]
  refine ⟨{ f := φp, comm' := ?_ }, ?_⟩
  · intro p q hpq
    have pq : q = p + 1 := by simpa only [ComplexShape.up_Rel] using hpq.symm
    subst q
    change φp p ≫ J.d p (p + 1) = G.map (I.d p (p + 1)) ≫ φp (p + 1)
    by_cases hp : p < i
    · have hz : G.map (I.d p (p + 1)) = 0 := by
        rw [(zi p hp).eq_of_src (I.d p (p + 1)) 0, G.map_zero]
      simp [φp, hp, hz]
    · have pn : P (p - i).toNat = p := by dsimp [P]; omega
      have qn : P ((p - i).toNat + 1) = p + 1 := by dsimp [P]; omega
      have hh := comm (p - i).toNat
      rw [← φP, ← φP, pn, qn] at hh
      exact hh
  · intro p
    change F.map (aI p) ≫ (φp p).f 0 = u.f p ≫ aJ p
    by_cases hp : p < i
    · have hz : eJ.f p = 0 := (zj p hp).eq_of_tgt _ _
      simp [φp, hp, aJ, hz]
    · have pn : P (p - i).toNat = p := by dsimp [P]; omega
      rw [← pn, φP]
      exact aug (p - i).toNat

end CategoryTheory
