/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Sheaf gluing for singleton-supported subset Čech cochains

Source: Stacks Project, Cohomology, Tag 08C1.
(blueprint: lem-sc-principal-open-cech-singleton-gluing).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Degree transport commutes with restriction and composes. -/
private theorem transport_restriction
    {A : Type u} [CommRing A]
    (J : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (a b c : ℤ) (hab : a = b) (hbc : b = c)
    (U V : (Spec (.of A)).Opens) (hUV : U ≤ V)
    (x : (modulesSpecToSheaf.obj (J.X a)).obj.obj (op V)) :
    (modulesSpecToSheaf.map (eqToHom (congrArg J.X hbc))).hom.app (op U)
      ((modulesSpecToSheaf.obj (J.X b)).obj.map (homOfLE hUV).op
        ((modulesSpecToSheaf.map (eqToHom (congrArg J.X hab))).hom.app (op V) x)) =
      (modulesSpecToSheaf.obj (J.X c)).obj.map (homOfLE hUV).op
        ((modulesSpecToSheaf.map (eqToHom (congrArg J.X (hab.trans hbc)))).hom.app
          (op V) x) := by
  subst b c
  simp only [eqToHom_refl]
  rfl

-- The pair calculation compares dependent section modules across degree and open transports.
/-- Singleton-supported cochains with no higher differential glue to sections.

Source: Stacks Project, Cohomology, Tag 08C1, initial exactness of the
augmented Čech row, and the sheaf gluing axiom.
(blueprint: lem-sc-principal-open-cech-singleton-gluing).

Proof: Transport each singleton coordinate of t to J.X n using hes, and
identify D({i}) with D(f i). On a two-element subset, the vertical term
is zero because t has no such component. The only horizontal terms are
the two singleton restrictions, with opposite signs. Since this component
of d(t) is zero, the singleton sections agree on D(f i) intersect D(f j).
For equal indices compatibility is reflexive; for indices in reverse order
reverse the equality. The sheaf gluing axiom on the union V supplies a
section s0. Set s to sigma_n inverse applied to s0. The stated augmentation
formula agrees with t at singleton coordinates by gluing, and both sides
vanish at larger coordinates. Injectivity of tau_n gives alpha_n(s)=t.
For r=0 the union is empty; the empty-family sheaf axiom supplies its unique
section, and the product of nonempty-subset coordinates is the zero module.
No injectivity hypothesis on the coefficient sheaves is used. -/
theorem principalOpenCech_singleton_gluing
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    :
    let V : (Spec (.of A)).Opens := ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i)
    let D : Finset (Fin r) → (Spec (.of A)).Opens :=
      fun S ↦ PrimeSpectrum.basicOpen (∏ j ∈ S, f j)
    ∀ (K T : CochainComplex (ModuleCat.{u} A) ℤ)
      (σ : ∀ n : ℤ, K.X n ≅ (modulesSpecToSheaf.obj (J.X n)).obj.obj (op V))
      (τ : ∀ n : ℤ, T.X n ≅ ModuleCat.of A
        (∀ S : {S : Finset (Fin r) // S.Nonempty},
          (modulesSpecToSheaf.obj (J.X (n + 1 - (S.val.card : ℤ)))).obj.obj (op (D S.val))))
      (α : K ⟶ T)
      (hle : ∀ (S : Finset (Fin r)) (j : Fin r), D S ≤ D (S.erase j))
      (hls : ∀ S : {S : Finset (Fin r) // S.Nonempty}, S.val.card = 1 → D S.val ≤ V)
      (he : ∀ (S : Finset (Fin r)) (j : Fin r), j ∈ S → ∀ n : ℤ,
        n + 1 - ((S.erase j).card : ℤ) = n + 1 + 1 - (S.card : ℤ))
      (hes : ∀ S : {S : Finset (Fin r) // S.Nonempty}, S.val.card = 1 → ∀ n : ℤ,
        n = n + 1 - (S.val.card : ℤ)),
      (∀ (n : ℤ) (s : T.X n) (S : {S : Finset (Fin r) // S.Nonempty}),
        (τ (n + 1)).hom (T.d n (n + 1) s) S =
          (-1 : A) ^ (S.val.card - 1) •
            (modulesSpecToSheaf.map
              (J.d (n + 1 - (S.val.card : ℤ)) (n + 1 + 1 - (S.val.card : ℤ)))).hom.app
                (op (D S.val)) ((τ n).hom s S) +
          ∑ j : S.val, if h : (S.val.erase j.val).Nonempty then
            (-1 : A) ^ ((S.val.filter (fun i ↦ i < j.val)).card) •
              (modulesSpecToSheaf.obj (J.X (n + 1 + 1 - (S.val.card : ℤ)))).obj.map
                (homOfLE (hle S.val j.val)).op
                ((modulesSpecToSheaf.map
                  (eqToHom (congrArg J.X (he S.val j.val j.property n)))).hom.app
                    (op (D (S.val.erase j.val))) ((τ n).hom s ⟨S.val.erase j.val, h⟩))
          else 0) →
      (∀ (n : ℤ) (s : K.X n) (S : {S : Finset (Fin r) // S.Nonempty}),
        (τ n).hom (α.f n s) S = if h : S.val.card = 1 then
          (modulesSpecToSheaf.obj (J.X (n + 1 - (S.val.card : ℤ)))).obj.map
            (homOfLE (hls S h)).op
            ((modulesSpecToSheaf.map (eqToHom (congrArg J.X (hes S h n)))).hom.app
              (op V) ((σ n).hom s)) else 0) →
      ∀ (n : ℤ) (t : T.X n),
        (∀ S : {S : Finset (Fin r) // S.Nonempty},
          1 < S.val.card → (τ n).hom t S = 0) →
        (∀ S : {S : Finset (Fin r) // S.Nonempty},
          1 < S.val.card → (τ (n + 1)).hom (T.d n (n + 1) t) S = 0) →
        ∃ s : K.X n, α.f n s = t := by
  classical
  dsimp only
  intro K T σ τ α hle hls he hes hT hα n t ht hdt
  let F := modulesSpecToSheaf.obj (J.X n)
  let U : Fin r → (Spec (.of A)).Opens := fun i ↦ PrimeSpectrum.basicOpen (f i)
  let singleton (i : Fin r) : {S : Finset (Fin r) // S.Nonempty} :=
    ⟨{i}, Finset.singleton_nonempty i⟩
  let sec (S : {S : Finset (Fin r) // S.Nonempty}) (hS : S.val.card = 1) :
      F.obj.obj (op (PrimeSpectrum.basicOpen (∏ j ∈ S.val, f j))) :=
    (modulesSpecToSheaf.map (eqToHom (congrArg J.X (hes S hS n).symm))).hom.app
      (op (PrimeSpectrum.basicOpen (∏ j ∈ S.val, f j))) ((τ n).hom t S)
  have hopen (i : Fin r) : U i =
      PrimeSpectrum.basicOpen (∏ j ∈ (singleton i).val, f j) := by simp [U, singleton]
  let sf (i : Fin r) : F.obj.obj (op (U i)) :=
    F.obj.map (eqToHom (hopen i)).op (sec (singleton i) (Finset.card_singleton i))
  have hlt (i j : Fin r) (hij : i < j) :
      F.obj.map (TopologicalSpace.Opens.infLELeft (U i) (U j)).op (sf i) =
        F.obj.map (TopologicalSpace.Opens.infLERight (U i) (U j)).op (sf j) := by
    let S : {S : Finset (Fin r) // S.Nonempty} := ⟨{i, j}, by simp⟩
    have hcard : S.val.card = 2 := Finset.card_pair (ne_of_lt hij)
    have hzero := hT n t S
    -- Simplify the dependent sum without constructing a rewrite motive for each step.
    simp only [ht S (by omega), map_zero, smul_zero, zero_add,
      hdt S (by omega)] at hzero
    have hsum (g : S.val → F.obj.obj
        (op (PrimeSpectrum.basicOpen (∏ j ∈ S.val, f j)))) :
        ∑ x : S.val, g x = g ⟨i, by simp [S]⟩ + g ⟨j, by simp [S]⟩ := by
      have huniv : (Finset.univ : Finset S.val) =
          {⟨i, by simp [S]⟩, ⟨j, by simp [S]⟩} := by
        ext x
        simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton]
        have hx := x.property
        simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hx | hx
        · exact Or.inl (Subtype.ext hx)
        · exact Or.inr (Subtype.ext hx)
      rw [huniv, Finset.sum_pair (by
        intro h; exact (ne_of_lt hij) (congrArg Subtype.val h))]
    -- Remove the integer-degree transport by composing with its inverse.
    let e := modulesSpecToSheaf.map
      (eqToHom (congrArg J.X (show n + 1 + 1 - (S.val.card : ℤ) = n by rw [hcard]; omega)))
    have hz := congrArg (fun z ↦ (e.hom.app
      (op (PrimeSpectrum.basicOpen (∏ j ∈ S.val, f j)))) z) hzero
    simp only [map_zero, map_sum] at hz
    simp only [hsum] at hz
    have hna : (S.val.erase i).Nonempty := by simp [S, hij.ne]
    have hnb : (S.val.erase j).Nonempty := by
      have hdel : S.val.erase j = {i} := by
        dsimp only [S]
        rw [Finset.pair_comm]
        simp [hij.ne']
      simp [hdel]
    simp only [dite_eq_left hna, dite_eq_left hnb] at hz
    have hpa : (S.val.filter (fun x ↦ x < i)).card = 0 := by
      simp [S, Finset.filter_insert, Finset.filter_singleton, hij.not_gt]
    have hpb : (S.val.filter (fun x ↦ x < j)).card = 1 := by
      simp [S, Finset.filter_insert, Finset.filter_singleton, hij]
    simp only [hpa, hpb, pow_zero, pow_one, one_smul, neg_one_smul, map_neg] at hz
    have hca : (S.val.erase i).card = 1 := by simp [S, hij.ne]
    have hcb : (S.val.erase j).card = 1 := by
      rw [show S.val.erase j = {i} by
        dsimp only [S]; rw [Finset.pair_comm]; simp [hij.ne']]
      simp
    have ha := transport_restriction J (n + 1 - ((S.val.erase i).card : ℤ))
      (n + 1 + 1 - (S.val.card : ℤ)) n (he S.val i (by simp [S]) n)
      (show n + 1 + 1 - (S.val.card : ℤ) = n by rw [hcard]; omega)
      _ _ (hle S.val i) ((τ n).hom t ⟨S.val.erase i, hna⟩)
    have hb := transport_restriction J (n + 1 - ((S.val.erase j).card : ℤ))
      (n + 1 + 1 - (S.val.card : ℤ)) n (he S.val j (by simp [S]) n)
      (show n + 1 + 1 - (S.val.card : ℤ) = n by rw [hcard]; omega)
      _ _ (hle S.val j) ((τ n).hom t ⟨S.val.erase j, hnb⟩)
    change _ = _ at hz
    rw [ha, hb] at hz
    have hz' : F.obj.map (homOfLE (hle S.val i)).op
        (sec ⟨S.val.erase i, hna⟩ hca) =
      F.obj.map (homOfLE (hle S.val j)).op (sec ⟨S.val.erase j, hnb⟩ hcb) :=
      (add_neg_eq_zero.mp hz.symm)
    have hD : U i ⊓ U j = PrimeSpectrum.basicOpen (∏ j ∈ S.val, f j) := by
      simp [S, U, Finset.prod_pair hij.ne, PrimeSpectrum.basicOpen_mul]
    have hr (B : {B : Finset (Fin r) // B.Nonempty}) (hB : B.val.card = 1)
        (k : Fin r) (hBk : B = singleton k)
        (hleB : PrimeSpectrum.basicOpen (∏ j ∈ S.val, f j) ≤
          PrimeSpectrum.basicOpen (∏ j ∈ B.val, f j))
        (hUk : U i ⊓ U j ≤ U k) :
        F.obj.map (eqToHom hD).op
          (F.obj.map (homOfLE hleB).op (sec B hB)) =
        F.obj.map (homOfLE hUk).op (sf k) := by
      subst B
      dsimp only [sf]
      change F.obj.map (eqToHom hD).op
        (F.obj.map (homOfLE hleB).op (sec (singleton k) hB)) =
        F.obj.map (homOfLE hUk).op
          (F.obj.map (eqToHom (hopen k)).op (sec (singleton k) hB))
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
      congr 2
    have hj' : (⟨S.val.erase i, hna⟩ : {B : Finset (Fin r) // B.Nonempty}) =
        singleton j := by apply Subtype.ext; simp [S, singleton, hij.ne]
    have hi' : (⟨S.val.erase j, hnb⟩ : {B : Finset (Fin r) // B.Nonempty}) =
        singleton i := by
      apply Subtype.ext
      dsimp only [S, singleton]
      rw [Finset.pair_comm]
      simp [hij.ne']
    have hh := congrArg (fun z ↦ F.obj.map (eqToHom hD).op z) hz'
    simp only [hr _ hca j hj' _ inf_le_right, hr _ hcb i hi' _ inf_le_left] at hh
    exact hh.symm
  have hcompat : TopCat.Presheaf.IsCompatible F.obj U sf := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact hlt i j hij
    · rfl
    · have hh := hlt j i hji
      have hh' := congrArg (fun z ↦ F.obj.map (eqToHom (inf_comm (U i) (U j))).op z)
        hh.symm
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp] at hh'
      exact hh'
  obtain ⟨s0, hs0, _⟩ := F.existsUnique_gluing U sf hcompat
  refine ⟨(σ n).inv s0, ?_⟩
  apply (ModuleCat.mono_iff_injective (τ n).hom).mp inferInstance
  funext S
  rw [hα]
  by_cases hS : S.val.card = 1
  · rw [dite_eq_left hS]
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hS
    have hSi : S = singleton i := Subtype.ext hi
    subst S
    let e := modulesSpecToSheaf.map
      (eqToHom (congrArg J.X (hes (singleton i) hS n).symm))
    apply (ModuleCat.mono_iff_injective (e.hom.app
      (op (PrimeSpectrum.basicOpen (∏ j ∈ (singleton i).val, f j))))).mp inferInstance
    rw [transport_restriction J n _ n (hes (singleton i) hS n)
      (hes (singleton i) hS n).symm]
    change F.obj.map (homOfLE (hls (singleton i) hS)).op
      ((modulesSpecToSheaf.map (eqToHom (congrArg J.X
        ((hes (singleton i) hS n).trans (hes (singleton i) hS n).symm)))).hom.app
          (op (⨆ i, U i)) ((σ n).hom ((σ n).inv s0))) = sec (singleton i) hS
    change F.obj.map (homOfLE (hls (singleton i) hS)).op
      ((σ n).hom ((σ n).inv s0)) = sec (singleton i) hS
    rw [Iso.inv_hom_id_apply]
    apply (ModuleCat.mono_iff_injective (F.obj.map (eqToHom (hopen i)).op)).mp
      inferInstance
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    have heq : eqToHom (hopen i) ≫ homOfLE (hls (singleton i) hS) =
        (TopologicalSpace.Opens.leSupr U i : U i ⟶ ⨆ j, U j) := Subsingleton.elim _ _
    rw [heq]
    exact hs0 i
  · rw [dite_eq_right hS]
    exact (ht S (by have := S.property.card_pos; omega)).symm

end AlgebraicGeometry
