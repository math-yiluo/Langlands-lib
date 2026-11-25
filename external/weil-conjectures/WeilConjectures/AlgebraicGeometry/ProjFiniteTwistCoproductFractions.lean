/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
public import WeilConjectures.Algebra.Module.DegreeZeroFractions
import WeilConjectures.Algebra.Module.FinitePiAwayFractions
import WeilConjectures.AlgebraicGeometry.ProjTwistBasicOpenFractions

/-!
# Basic-open fractions for finite coproducts of Proj twists

Source: Stacks Project, Constructions, Tags 01M6 (3), 01M7 (2),(3), 01MN (1).
(blueprint: lem-sc-proj-finite-twist-coproduct-fractions)
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite LocalizedModule

namespace AlgebraicGeometry.Proj

private noncomputable def coproductProjection {X : AlgebraicGeometry.Scheme.{v}}
    {r : ℕ} (F : Fin r → X.Modules) (i : Fin r) : ∐ F ⟶ F i := by
  letI : HasFiniteBiproducts X.Modules := Abelian.hasFiniteBiproducts
  exact (biproduct.isoCoproduct F).inv ≫ biproduct.π F i

private noncomputable def coproductCoordinates {X : AlgebraicGeometry.Scheme.{v}}
    {r : ℕ} (F : Fin r → X.Modules) (U : X.Opens) :
    Γ(∐ F, U) →+ (∀ i, Γ(F i, U)) :=
  AddMonoidHom.pi fun i ↦ ((coproductProjection F i).app U).hom

private theorem modules_sum_app {X : AlgebraicGeometry.Scheme.{v}}
    {M N : X.Modules} {ι : Type} (S : Finset ι) (p : ι → (M ⟶ N))
    (U : X.Opens) (s : Γ(M, U)) :
    (∑ i ∈ S, p i).app U s = ∑ i ∈ S, (p i).app U s := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => simp [hi, Scheme.Modules.Hom.add_app, ih]

private theorem coproductCoordinates_bijective {X : AlgebraicGeometry.Scheme.{v}}
    {r : ℕ} (F : Fin r → X.Modules) (U : X.Opens) :
    Function.Bijective (coproductCoordinates F U) := by
  let : HasFiniteBiproducts X.Modules := Abelian.hasFiniteBiproducts
  classical
  have total : ∑ i, coproductProjection F i ≫ Sigma.ι F i = 𝟙 (∐ F) := by
    apply (cancel_epi (biproduct.isoCoproduct F).hom).mp
    simp only [Preadditive.comp_sum, coproductProjection, ← Category.assoc,
      Iso.hom_inv_id, Category.id_comp, Category.comp_id]
    rw [biproduct.isoCoproduct_hom, biproduct.desc_eq]
  have total_app (s : Γ(∐ F, U)) :
      ∑ i, (Sigma.ι F i).app U ((coproductProjection F i).app U s) = s := by
    have ht := congrArg (fun p : ∐ F ⟶ ∐ F ↦ p.app U s) total
    simpa [modules_sum_app] using ht
  refine ⟨?_, ?_⟩
  · intro s t h
    rw [← total_app s, ← total_app t]
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg ((Sigma.ι F i).app U) (congrFun h i)
  · intro s
    refine ⟨∑ i, (Sigma.ι F i).app U (s i), ?_⟩
    ext j
    change (coproductProjection F j).app U (∑ i, (Sigma.ι F i).app U (s i)) = s j
    rw [map_sum]
    rw [Finset.sum_eq_single j]
    · change ((Sigma.ι F j ≫ coproductProjection F j).app U) (s j) = s j
      simp [coproductProjection, biproduct.isoCoproduct_inv]
    · intro i _ hij
      change ((Sigma.ι F i ≫ coproductProjection F j).app U) (s i) = 0
      simp [coproductProjection, biproduct.isoCoproduct_inv, hij]
    · simp


/-- For any graded commutative ring, the finite coproduct of its twists is the
associated sheaf of the finite sum of shifts, with scalar-compatible fraction maps.
Source: Stacks Project, Constructions, Tags 01M6 (3), 01M7 (2),(3), 01MN (1).
(blueprint: lem-sc-proj-finite-twist-coproduct-fractions)

Proof: identify the sections of each twist on D₊(f) with degree-zero fractions
of A(a i), by 01MN (1) and 01M7 (2). Finite coproducts of modules are finite
products, and finite products of sheaves are computed on sections. Thus send
a tuple of sections to its componentwise fractions, viewed in the localization
of Fin r → A. Localization commutes with this finite product: choose a common
power f^m for the finitely many denominators, multiplying the i-th numerator
by the missing power of f. This gives an additive injection. A tuple of
homogeneous fractions with common denominator f^m has numerator degree
a i + m * b in component i. Conversely every tuple satisfying those degree
conditions gives sections of each twist, proving the range equality. When r = 0,
both sides are zero, and choose numerator zero and denominator 1.
The scalar action is multiplication in the localization, so the fraction map
intertwines awayToSection q with the algebra map of q. For a restriction with
g^e = h * f, multiply a numerator y over f^m by h^m; the new denominator is
g^(e*m), since (g^e)^m = h^m * f^m. This is the canonical localization map
of 01M7 (3), hence agrees with the sheaf restriction on every component. -/
theorem finite_twist_coproduct_fractions
    {A σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (r : ℕ) (a : Fin r → ℤ) :
  ∃ alpha : ∀ (f : A) (b : ℕ),
    0 < b → f ∈ 𝒜 b →
    (∐ (fun i : Fin r ↦ twist 𝒜 (a i))).val.obj (op (basicOpen 𝒜 f))
      →+ LocalizedModule.Away f (Fin r → A),
  (∀ (f : A) (b : ℕ) (hb : 0 < b)
    (hf : f ∈ 𝒜 b),
    Function.Injective (alpha f b hb hf) ∧
    Set.range (alpha f b hb hf) = degreeZeroFractions
      (fun n : ℕ ↦ (𝒜 n : Set _))
      (fun n : ℕ ↦ {y : Fin r → A | ∀ i,
        if 0 ≤ a i + n then
          y i ∈ 𝒜 (a i + n).toNat
        else y i = 0}) (Submonoid.powers f)) ∧
  (∀ (f : A) (b : ℕ) (hb : 0 < b)
    (hf : f ∈ 𝒜 b)
    (q : HomogeneousLocalization.Away 𝒜 f)
    (s : (∐ (fun i : Fin r ↦ twist 𝒜 (a i))).val.obj (op (basicOpen 𝒜 f))),
    alpha f b hb hf (awayToSection 𝒜 f q
      • s) = algebraMap
        (HomogeneousLocalization.Away 𝒜 f)
        (Localization.Away f) q • alpha f b hb hf s) ∧
  (∀ (f g : A) (b c : ℕ) (hb : 0 < b) (hc : 0 < c)
    (hf : f ∈ 𝒜 b)
    (hg : g ∈ 𝒜 c)
    (inc : basicOpen 𝒜 g ≤
      basicOpen 𝒜 f)
    (e t : ℕ) (h : A),
    0 < e → h ∈ 𝒜 t → g ^ e = h * f →
    ∀ (m : ℕ) (y : Fin r → A)
      (s : (∐ (fun i : Fin r ↦ twist 𝒜 (a i))).val.obj
          (op (basicOpen 𝒜 f))),
      alpha f b hb hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
      alpha g c hc hg ((∐ (fun i : Fin r ↦
        twist 𝒜 (a i))).val.map
          (homOfLE inc).op s) =
        mk (h ^ m • y) (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g)) := by
  classical
  obtain ⟨beta, hbeta, hscalar, hrestrict⟩ := single_twist_basicOpen_fractions 𝒜
  let F : Fin r → (Proj 𝒜).Modules := fun i ↦ twist 𝒜 (a i)
  have hpi (f : A) := awayPi_bijective_degreeZero 𝒜 r a f
  let E (f : A) :=
    AddEquiv.ofBijective (awayPi r f).toAddMonoidHom (hpi f).1
  let gamma (f : A) (b : ℕ) (hb : 0 < b) (hf : f ∈ 𝒜 b) :
      (∐ F).val.obj (op (basicOpen 𝒜 f)) →+ (Fin r → LocalizedModule.Away f A) :=
    AddMonoidHom.pi fun i ↦ (beta (a i) f b hb hf).comp
      (((coproductProjection F i).app (basicOpen 𝒜 f)).hom)
  let alpha (f : A) (b : ℕ) (hb : 0 < b) (hf : f ∈ 𝒜 b) :=
    (E f).symm.toAddMonoidHom.comp (gamma f b hb hf)
  have coord (f : A) (b : ℕ) (hb : 0 < b) (hf : f ∈ 𝒜 b)
      (s : (∐ F).val.obj (op (basicOpen 𝒜 f))) (i : Fin r) :
      awayPi r f (alpha f b hb hf s) i =
        beta (a i) f b hb hf ((coproductProjection F i).app (basicOpen 𝒜 f) s) := by
    exact congrFun ((E f).apply_symm_apply (gamma f b hb hf s)) i
  refine ⟨alpha, ?_, ?_, ?_⟩
  · intro f b hb hf
    refine ⟨?_, ?_⟩
    · intro s t h
      apply (coproductCoordinates_bijective F (basicOpen 𝒜 f)).1
      ext i
      apply (hbeta (a i) f b hb hf).1
      change beta (a i) f b hb hf
        ((coproductProjection F i).app (basicOpen 𝒜 f) s) =
          beta (a i) f b hb hf ((coproductProjection F i).app (basicOpen 𝒜 f) t)
      rw [← coord, ← coord, h]
    · ext x
      constructor
      · rintro ⟨s, rfl⟩
        apply ((hpi f).2 _).2
        intro i
        rw [coord, ← (hbeta (a i) f b hb hf).2]
        exact ⟨_, rfl⟩
      · intro hx
        have hx' := ((hpi f).2 x).1 hx
        have hs (i : Fin r) : ∃ s, beta (a i) f b hb hf s = awayPi r f x i := by
          exact (Set.ext_iff.mp (hbeta (a i) f b hb hf).2 _).mpr (hx' i)
        choose s hs using hs
        obtain ⟨t, ht⟩ := (coproductCoordinates_bijective F (basicOpen 𝒜 f)).2 s
        refine ⟨t, (hpi f).1.1 ?_⟩
        ext i
        rw [coord]
        exact (congrArg (beta (a i) f b hb hf) (congrFun ht i)).trans (hs i)
  · intro f b hb hf q s
    apply (hpi f).1.1
    ext i
    rw [awayPi_smul, Pi.smul_apply, coord, coord,
      Scheme.Modules.Hom.app_smul, hscalar]
  · intro f g b c hb hc hf hg inc e t h he hh heq m y s hs
    apply (hpi g).1.1
    ext i
    rw [coord, awayPi_mk]
    have natural := PresheafOfModules.naturality_apply
      (coproductProjection F i).val (homOfLE inc).op s
    change beta (a i) g c hc hg
      ((coproductProjection F i).val.app (op (basicOpen 𝒜 g))
        ((∐ F).val.map (homOfLE inc).op s)) = _
    rw [natural]
    apply hrestrict (a i) f g b c hb hc hf hg inc e t h he hh heq m (y i)
    have hs' := congrArg (fun x ↦ awayPi r f x i) hs
    rw [coord, awayPi_mk] at hs'
    exact hs'


end AlgebraicGeometry.Proj
