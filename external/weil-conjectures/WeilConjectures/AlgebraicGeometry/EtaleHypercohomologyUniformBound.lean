/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Colimits
public import WeilConjectures.AlgebraicGeometry.EtaleTermwiseHypercohomology
import WeilConjectures.AlgebraicGeometry.EtaleHypercohomologySupportedResolutionMaps
import WeilConjectures.AlgebraicGeometry.EtaleKInjectivePullbackAbutment
import WeilConjectures.AlgebraicGeometry.DerivedEtaleCohomologyPullbackLaws
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import WeilConjectures.Algebra.Homology.KInjectiveResolution
/-! # Quantitative stabilization for functorial hypercohomology

Source: Stacks Project, Tags 015J and 0EZM.
(blueprint: lem-weil-pbc-hypercohomology-uniform-bound).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
private theorem spectralSequence_ext_first_aux
    (_ : True) {C : Type*} [Category C] [Abelian C] {κ : Type*}
    {c : ℤ → ComplexShape κ} {r₀ : ℤ} {E E' : SpectralSequence C c r₀}
    {f g : E ⟶ E'} (h : f.hom r₀ le_rfl = g.hom r₀ le_rfl) : f = g := by
  apply SpectralSequence.hom_ext
  intro r hr
  induction r, hr using Int.leInduction with
  | base => exact h
  | succ r hr ih =>
    apply HomologicalComplex.hom_ext
    intro pq
    apply (cancel_epi (E.iso r (r + 1) pq rfl hr).hom).mp
    rw [← f.comm r (r + 1) pq rfl hr, ← g.comm r (r + 1) pq rfl hr, ih]

set_option backward.isDefEq.respectTransparency false in
private theorem sections_naturality {X Y : Scheme.{u}} (f : Y ⟶ X)
    {A B : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (g : A ⟶ B) :
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).map g ≫
      globalSectionsUpperStarMap AddCommGrpCat.{u + 1} f B =
    globalSectionsUpperStarMap AddCommGrpCat.{u + 1} f A ≫
      (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        ((upperStar AddCommGrpCat.{u + 1} f).map g) := by
  unfold globalSectionsUpperStarMap
  rw [Category.assoc, Category.assoc,
    (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}
      terminalIsTerminal).hom.naturality_assoc g]
  have hn := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.naturality g
  simp only [Functor.id_map] at hn
  rw [← Functor.map_comp_assoc, hn, Functor.map_comp]
  simp only [Category.assoc]
  rw [← (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}
      terminalIsTerminal).inv.naturality]
  congr 1
  congr 1
  have hu := ((upperStar AddCommGrpCat.{u + 1} f).map g).hom.naturality
    (PreservesTerminal.iso (Scheme.Hom.Etale f)).inv.op
  simp only [Functor.comp_map, Functor.flip_obj_map, ObjectProperty.ι_map]
  erw [lowerStar_map_hom_app]
  simpa only [Category.assoc] using! congrArg (fun a ↦ a ≫
    (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}
      terminalIsTerminal).inv.app ((upperStar AddCommGrpCat.{u + 1} f).obj B)) hu.symm

set_option backward.isDefEq.respectTransparency false in
-- Elaborate the dependent page and presentation families.
set_option linter.unusedVariables false in
/-- Functorial termwise presentations can be chosen with a quantitative stabilization bound.
Source: Stacks Project, Tags 015J, 015K and 0EZM.

Proof: Choose the Cartan--Eilenberg resolutions and comparison maps as in
`exists_etaleHypercohomology_pullback_functorial`. For a complex zero below a, choose
its resolution zero in these rows. On the first page the support is q >= a and the
resolution degree is nonnegative. In bidegree (q,n-q), an outgoing differential has
negative resolution degree once r > n-q+1; an incoming differential originates
below row a once r > q-a. Consequently both differentials vanish at and after
max 1 (max (q-a+2) (n-q+2)). The finite filtered total-complex construction identifies
this stationary term with its canonical abutment graded piece. Define R to be the
least stabilization threshold at least 1, and use the canonical stationary identifications.
The support estimate bounds R for every valid a. Filtered comparison maps commute
with all these identifications, giving the first-page, abutment, identity and
composition equations of the functorial presentation theorem unchanged.
(blueprint: lem-weil-pbc-hypercohomology-uniform-bound). -/
theorem exists_etaleHypercohomology_uniform_bound
    (P : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
      (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
      (L : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
      (_ : ((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K ⟶ L) (n : ℤ),
      (cohomology AddCommGrpCat.{u + 1} X n).obj (DerivedCategory.Q.obj K) ⟶
        (cohomology AddCommGrpCat.{u + 1} Y n).obj (DerivedCategory.Q.obj L))
    (hP : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
      (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
      (L : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
      (v : ((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K ⟶ L) (n : ℤ),
      P f K L v n = (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).map
        ((rightDerivedGlobalSections AddCommGrpCat.{u + 1} X).map
            ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
              (DerivedCategory.Q.obj K)) ≫
          (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
            AddCommGrpCat.{u + 1} f).hom.app
              ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategory.obj
                (DerivedCategory.Q.obj K)) ≫
          (rightDerivedGlobalSections AddCommGrpCat.{u + 1} Y).map
            ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryFactors.hom.app K ≫
              DerivedCategory.Q.map v))) :
    ∃ (D : ∀ (X : Scheme.{u})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})),
        EtaleTermwiseHypercohomology X K)
      (M : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (v : ((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj),
        (D X K).sequence ⟶ (D Y L).sequence)
      (R : ∀ (X : Scheme.{u})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (q n : ℤ), ℤ)
      (eInf : ∀ (X : Scheme.{u})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (q n r : ℤ) (hr : 1 ≤ r) (hR : R X K q n ≤ r),
        ((D X K).sequence.page r hr).X (q, n - q) ≅ ((D X K).H n).gradedPiece q),
      (      (∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (v : ((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj) (p : ℕ) (q : ℤ),
        ((M f K L v).hom 1).f (q, (p : ℤ)) ≫ ((D Y L).firstPageIso p q).hom =
          ((D X K).firstPageIso p q).hom ≫
            AddCommGrpCat.ofHom ((Sheaf.H.map (v.f q) p).comp
              (cohomologyMap f (K.obj.X q) p))) ∧
      (∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (v : ((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj) (n : ℤ),
        ∃ (t : ∀ q : ℤ, (((D X K).H n).step q : AddCommGrpCat.{u + 1}) ⟶
            (((D Y L).H n).step q : AddCommGrpCat.{u + 1}))
          (ht : ∀ q : ℤ, t q ≫ (((D Y L).H n).step q).arrow =
            (((D X K).H n).step q).arrow ≫ P f K.obj L.obj v n)
          (hc : ∀ q : ℤ,
            Subobject.ofLE (((D X K).H n).step (q + 1)) (((D X K).H n).step q)
                (((D X K).H n).antitone_step (Int.le_add_one (le_refl q))) ≫ t q =
              t (q + 1) ≫
                Subobject.ofLE (((D Y L).H n).step (q + 1)) (((D Y L).H n).step q)
                  (((D Y L).H n).antitone_step (Int.le_add_one (le_refl q)))),
          ∀ (q r : ℤ) (hr : 1 ≤ r) (hX : R X K q n ≤ r) (hY : R Y L q n ≤ r),
            ((M f K L v).hom r hr).f (q, n - q) ≫ (eInf Y L q n r hr hY).hom =
              (eInf X K q n r hr hX).hom ≫
                cokernel.map
                  (Subobject.ofLE (((D X K).H n).step (q + 1)) (((D X K).H n).step q)
                    (((D X K).H n).antitone_step (Int.le_add_one (le_refl q))))
                  (Subobject.ofLE (((D Y L).H n).step (q + 1)) (((D Y L).H n).step q)
                    (((D Y L).H n).antitone_step (Int.le_add_one (le_refl q))))
                  (t (q + 1)) (t q) (hc q)) ∧
      (∀ (X : Scheme.{u})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})),
        M (𝟙 X) K K
            ((NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{u + 1} X)
              (ComplexShape.up ℤ) ≪≫ Functor.mapHomologicalComplexIdIso
                (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
                  (ComplexShape.up ℤ)).hom.app K.obj) = 𝟙 (D X K).sequence ∧
          ∀ n : ℤ, P (𝟙 X) K.obj K.obj
            ((NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{u + 1} X)
              (ComplexShape.up ℤ) ≪≫ Functor.mapHomologicalComplexIdIso
                (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
                  (ComplexShape.up ℤ)).hom.app K.obj) n = 𝟙 _) ∧
      (∀ {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (N : CochainComplex.Plus (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (v : ((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj)
        (w : ((upperStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L.obj ⟶ N.obj),
        M (g ≫ f) K N
            ((Functor.mapHomologicalComplexCompIso
              (upperStarComp AddCommGrpCat.{u + 1} g f).symm
                (ComplexShape.up ℤ)).inv.app K.obj ≫
              ((upperStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex
                (ComplexShape.up ℤ)).map v ≫ w) = M f K L v ≫ M g L N w ∧
          ∀ n : ℤ, P (g ≫ f) K.obj N.obj
            ((Functor.mapHomologicalComplexCompIso
              (upperStarComp AddCommGrpCat.{u + 1} g f).symm
                (ComplexShape.up ℤ)).inv.app K.obj ≫
              ((upperStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex
                (ComplexShape.up ℤ)).map v ≫ w) n =
            P f K.obj L.obj v n ≫
              P g L.obj N.obj w n)) ∧
      (∀ (X : Scheme.{u})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (a q n : ℤ), (∀ s : ℤ, s < a → IsZero (K.obj.X s)) →
        R X K q n ≤ max 1 (max (q - a + 2) (n - q + 2))) := by
  classical
  obtain ⟨D, M, eSupported, hE, hA⟩ :=
    exists_etaleHypercohomology_supported_resolution_maps
  -- An admissible page has a support witness; this property is upward closed.
  let admissible (X : Scheme.{u})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
      (q n r : ℤ) : Prop :=
    ∃ a : ℤ, (∀ s : ℤ, s < a → IsZero (K.obj.X s)) ∧
      max 1 (max (q - a + 2) (n - q + 2)) ≤ r
  have exists_admissible (X : Scheme.{u})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
      (q n : ℤ) : ∃ k : ℕ, admissible X K q n k := by
    obtain ⟨a, ha⟩ := K.property
    let b := max 1 (max (q - a + 2) (n - q + 2))
    have hb : 0 ≤ b := le_trans (by decide : (0 : ℤ) ≤ 1) (le_max_left _ _)
    refine ⟨b.toNat, a, ?_, ?_⟩
    · intro s hs
      exact K.obj.isZero_of_isStrictlyGE a s hs
    · dsimp only [b]
      rw [Int.toNat_of_nonneg hb]
  let R (X : Scheme.{u})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
      (q n : ℤ) : ℤ := Nat.find (exists_admissible X K q n)
  have in_range (X : Scheme.{u})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
      (q n r : ℤ) (hR : R X K q n ≤ r) : admissible X K q n r := by
    obtain ⟨a, ha, hb⟩ := Nat.find_spec (exists_admissible X K q n)
    exact ⟨a, ha, le_trans hb hR⟩
  have bound (X : Scheme.{u})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
      (a q n : ℤ) (ha : ∀ s : ℤ, s < a → IsZero (K.obj.X s)) :
      R X K q n ≤ max 1 (max (q - a + 2) (n - q + 2)) := by
    let b := max 1 (max (q - a + 2) (n - q + 2))
    have hb : 0 ≤ b := le_trans (by decide : (0 : ℤ) ≤ 1) (le_max_left _ _)
    have hfind : Nat.find (exists_admissible X K q n) ≤ b.toNat :=
      Nat.find_min' (exists_admissible X K q n)
        ⟨a, ha, by rw [Int.toNat_of_nonneg hb]⟩
    have hcast : (Nat.find (exists_admissible X K q n) : ℤ) ≤ (b.toNat : ℤ) :=
      Int.ofNat_le.mpr hfind
    simpa only [R, Int.toNat_of_nonneg hb] using hcast
  let eInf := fun X K q n r hr hR ↦
    eSupported X K q n r hr (in_range X K q n r hR)
  obtain ⟨hPid, hPcomp⟩ := derivedEtaleCohomology_pullback_laws P hP
  refine ⟨D, (fun f K L v ↦ M f K L v), R, eInf, ⟨hE, ?_, ?_, ?_⟩, bound⟩
  · intro X Y f K L v n
    let := (D X K).ρ.quasiIso
    let := (D Y L).ρ.isKInjective
    let F := (upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)
    let Q := HomotopyCategory.quotient
      (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ)
    have hbij := CochainComplex.IsKInjective.bijective_quotient_map_comp (J := (D Y L).ρ.complex)
        (F.map (D X K).ρ.map)
    obtain ⟨a, ha⟩ := hbij.surjective (Q.map (v ≫ (D Y L).ρ.map))
    obtain ⟨j, rfl⟩ := Q.map_surjective a
    have hj : Nonempty (Homotopy (F.map (D X K).ρ.map ≫ j)
        (v ≫ (D Y L).ρ.map)) := by
      refine ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩
      simpa only [Functor.map_comp] using ha
    let w : ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (D X K).ρ.complex ⟶
        ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (D Y L).ρ.complex :=
      { f := fun i ↦ globalSectionsUpperStarMap AddCommGrpCat.{u + 1} f
            ((D X K).ρ.complex.X i) ≫
          (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map (j.f i)
        comm' := by
          intro i k hik
          change (_ ≫ _) ≫
              (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map
                ((D Y L).ρ.complex.d i k) =
            (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
              ((D X K).ρ.complex.d i k) ≫ _
          rw [Category.assoc, ← Functor.map_comp, j.comm i k, Functor.map_comp]
          simp only [F, Functor.mapHomologicalComplex_obj_d]
          rw [← Category.assoc, ← sections_naturality f, Category.assoc] }
    have hw : ∀ i : ℤ, w.f i =
        globalSectionsUpperStarMap AddCommGrpCat.{u + 1} f ((D X K).ρ.complex.X i) ≫
          (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map (j.f i) :=
      fun _ ↦ rfl
    obtain ⟨t, ht, hstable⟩ := hA f K L v n j hj w hw
    have hmap := etaleKInjective_pullback_abutment f K.obj L.obj v
      (D X K).ρ (D Y L).ρ j hj w hw n
    have hPmap := hP f K.obj L.obj v n
    have ht' : ∀ q : ℤ, t q ≫ (((D Y L).H n).step q).arrow =
        (((D X K).H n).step q).arrow ≫ P f K.obj L.obj v n := by
      intro q
      rw [hPmap, ← hmap]
      exact ht q
    have hc : ∀ q : ℤ,
        Subobject.ofLE (((D X K).H n).step (q + 1)) (((D X K).H n).step q)
            (((D X K).H n).antitone_step (Int.le_add_one (le_refl q))) ≫ t q =
          t (q + 1) ≫
            Subobject.ofLE (((D Y L).H n).step (q + 1)) (((D Y L).H n).step q)
              (((D Y L).H n).antitone_step (Int.le_add_one (le_refl q))) := by
      intro q
      apply (cancel_mono (((D Y L).H n).step q).arrow).1
      rw [Category.assoc, ht', Category.assoc, Subobject.ofLE_arrow, ht',
        ← Category.assoc, Subobject.ofLE_arrow]
    refine ⟨t, ht', hc, ?_⟩
    intro q r hr hX hY
    exact hstable hc q r hr (in_range X K q n r hX) (in_range Y L q n r hY)
  · intro X K
    refine ⟨?_, hPid X K⟩
    apply spectralSequence_ext_first_aux trivial
    apply HomologicalComplex.hom_ext
    rintro ⟨q, p⟩
    by_cases hp : 0 ≤ p
    · lift p to ℕ using hp
      apply (cancel_mono ((D X K).firstPageIso p q).hom).mp
      rw [hE]
      simp only [SpectralSequence.id_hom, HomologicalComplex.id_f, Category.id_comp]
      have hid := (cohomologyPullbackFunctorial (𝟙 X) (𝟙 X) (K.obj.X q) p).2.2
      suffices h : AddCommGrpCat.ofHom
          ((Sheaf.H.map _ p).comp (cohomologyMap (𝟙 X) (K.obj.X q) p)) = 𝟙 _ by
        simpa using congrArg (((D X K).firstPageIso p q).hom ≫ ·) h
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro x
      change Sheaf.H.map
        ((upperStarId AddCommGrpCat.{u + 1} X).hom.app (K.obj.X q) ≫ 𝟙 _) p
          (cohomologyMap (𝟙 X) (K.obj.X q) p x) = x
      simpa only [Category.comp_id] using hid x
    · exact ((D X K).negative q p (by omega)).eq_of_src _ _
  · intro X Y Z f g K L N v w
    refine ⟨?_, hPcomp f g K L N v w⟩
    apply spectralSequence_ext_first_aux trivial
    apply HomologicalComplex.hom_ext
    rintro ⟨q, p⟩
    by_cases hp : 0 ≤ p
    · lift p to ℕ using hp
      apply (cancel_mono ((D Z N).firstPageIso p q).hom).mp
      simp only [SpectralSequence.comp_hom, HomologicalComplex.comp_f, Category.assoc]
      rw [hE, hE]
      simp only [← Category.assoc]
      rw [hE]
      simp only [Category.assoc]
      apply congrArg (((D X K).firstPageIso p q).hom ≫ ·)
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro x
      have hcomp := (cohomologyPullbackFunctorial g f (K.obj.X q) p).2.1 x
      have hnat := cohomologyMap_map g p (v.f q)
        (cohomologyMap f (K.obj.X q) p x)
      change Sheaf.H.map
        (((upperStarComp AddCommGrpCat.{u + 1} g f).hom.app (K.obj.X q) ≫
          (upperStar AddCommGrpCat.{u + 1} g).map (v.f q)) ≫ w.f q) p
          (cohomologyMap (g ≫ f) (K.obj.X q) p x) =
        Sheaf.H.map (w.f q) p (cohomologyMap g (L.obj.X q) p
          (Sheaf.H.map (v.f q) p (cohomologyMap f (K.obj.X q) p x)))
      simp only [Sheaf.H.map_comp_apply]
      rw [← hcomp]
      exact congrArg (Sheaf.H.map (w.f q) p) hnat.symm
    · exact ((D X K).negative q p (by omega)).eq_of_src _ _

end AlgebraicGeometry.Etale
