/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.RingTheory.Localization.AtPrime.Basic

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The localization colimit construction required for the filtered-colimit theorem.

The proof follows the fraction construction for Tag 037D: induced maps between the
localizations at contracted primes form a functor, and the canonical localization of
the colimit is its colimit.  The detailed fraction and filteredness argument is split
into this intermediate statement for independent formalization.
(blueprint: lemma-quasi-finite-coordinates--1)
The proof is the standard fraction construction: represent numerators and denominators
at a common filtered stage, lift equality witnesses to a later stage, and apply the
universal property of the filtered colimit. -/
theorem filteredColimitLocalizationAtPrime_data
    {I : Type v} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommRingCat.{v}) [HasColimit F]
    (p : Ideal ((colimit F : CommRingCat) : Type v)) [hp : p.IsPrime] :
    let ι : ∀ i : I, (F.obj i) ⟶ colimit F := fun i => colimit.ι F i
    let pᵢ : ∀ i : I, Ideal ((F.obj i : CommRingCat) : Type v) :=
      fun i => Ideal.comap (ι i).hom p
    ∃ (D : I ⥤ CommRingCat.{v})
      (hD : ∀ i : I, D.obj i = CommRingCat.of (Localization.AtPrime (pᵢ i))),
      (∀ (i j : I) (a : i ⟶ j),
        CommRingCat.ofHom (algebraMap (F.obj i) (Localization.AtPrime (pᵢ i))) ≫
            eqToHom (hD i).symm ≫ D.map a =
          F.map a ≫
            CommRingCat.ofHom (algebraMap (F.obj j) (Localization.AtPrime (pᵢ j))) ≫
            eqToHom (hD j).symm) ∧
      ∃ (c : Cocone D) (hc : c.pt = CommRingCat.of (Localization.AtPrime p)),
        (∀ i : I,
          CommRingCat.ofHom (algebraMap (F.obj i) (Localization.AtPrime (pᵢ i))) ≫
              eqToHom (hD i).symm ≫ c.ι.app i ≫ eqToHom hc =
            ι i ≫ CommRingCat.ofHom
              (algebraMap ((colimit F : CommRingCat) : Type v)
                (Localization.AtPrime p))) ∧
        Nonempty (IsColimit c) := by
  classical
  let ι : ∀ i : I, (F.obj i) ⟶ colimit F := fun i ↦ colimit.ι F i
  let q : ∀ i : I, Ideal (F.obj i) := fun i ↦ Ideal.comap (ι i).hom p
  have hq (i j : I) (a : i ⟶ j) : q i = Ideal.comap (F.map a).hom (q j) := by
    change Ideal.comap (colimit.ι F i).hom p =
      Ideal.comap (F.map a).hom (Ideal.comap (colimit.ι F j).hom p)
    rw [Ideal.comap_comap]
    congr 1
    exact congrArg CommRingCat.Hom.hom (colimit.w F a).symm
  -- Localization maps are determined by their restrictions to the original rings.
  let D : I ⥤ CommRingCat.{v} :=
    { obj := fun i ↦ CommRingCat.of (Localization.AtPrime (q i))
      map := fun {i j} a ↦ CommRingCat.ofHom
        (Localization.localRingHom (q i) (q j) (F.map a).hom (hq i j a))
      map_id := by
        intro i
        ext1
        apply IsLocalization.ringHom_ext (q i).primeCompl
        ext x
        simp
      map_comp := by
        intro i j k a b
        ext1
        apply IsLocalization.ringHom_ext (q i).primeCompl
        ext x
        simp }
  have hmap (i j : I) (a : i ⟶ j) (x : F.obj i) :
      (D.map a).hom (algebraMap (F.obj i) (Localization.AtPrime (q i)) x) =
        algebraMap (F.obj j) (Localization.AtPrime (q j)) ((F.map a).hom x) := by
    exact Localization.localRingHom_to_map (q i) (q j) (F.map a).hom (hq i j a) x
  let κ : ∀ i : I, D.obj i ⟶ CommRingCat.of (Localization.AtPrime p) := fun i ↦
    CommRingCat.ofHom (Localization.localRingHom (q i) p (ι i).hom rfl)
  have hκ (i : I) (x : F.obj i) :
      (κ i).hom (algebraMap (F.obj i) (Localization.AtPrime (q i)) x) =
        algebraMap ((colimit F : CommRingCat) : Type v) (Localization.AtPrime p) ((ι i).hom x) := by
    exact Localization.localRingHom_to_map (q i) p (ι i).hom rfl x
  let c : Cocone D :=
    { pt := CommRingCat.of (Localization.AtPrime p)
      ι :=
        { app := κ
          naturality := by
            intro i j a
            dsimp
            ext1
            apply IsLocalization.ringHom_ext (q i).primeCompl
            ext x
            change (κ j).hom ((D.map a).hom (algebraMap _ _ x)) =
              (κ i).hom (algebraMap _ _ x)
            rw [hmap, hκ, hκ]
            exact congrArg
              (algebraMap ((colimit F : CommRingCat) : Type v) (Localization.AtPrime p))
              (ConcreteCategory.congr_hom (colimit.w F a) x) } }
  refine ⟨D, fun _ ↦ rfl, ?_, c, rfl, ?_, ?_⟩
  · intro i j a
    ext x
    exact hmap i j a x
  · intro i
    ext x
    exact hκ i x
  -- Restrict a cocone to F, then extend its colimit map across the localization.
  · let U : Cocone D → Cocone F := fun s ↦
      { pt := s.pt
        ι :=
          { app := fun i ↦
              CommRingCat.ofHom (algebraMap (F.obj i) (Localization.AtPrime (q i))) ≫
                s.ι.app i
            naturality := by
              intro i j a
              dsimp
              ext x
              change (s.ι.app j).hom (algebraMap _ _ ((F.map a).hom x)) =
                (s.ι.app i).hom (algebraMap _ _ x)
              rw [← hmap]
              exact ConcreteCategory.congr_hom (s.w a) (algebraMap _ _ x) } }
    let f : ∀ s : Cocone D, colimit F ⟶ s.pt := fun s ↦ colimit.desc F (U s)
    have hf (s : Cocone D) (i : I) (x : F.obj i) :
        (f s).hom ((ι i).hom x) = (s.ι.app i).hom (algebraMap _ _ x) := by
      exact ConcreteCategory.congr_hom (colimit.ι_desc (U s) i) x
    -- Every denominator comes from a stage, where it is already invertible.
    have hu (s : Cocone D) (y : p.primeCompl) : IsUnit ((f s).hom y) := by
      obtain ⟨i, x, hx⟩ := Types.jointly_surjective_of_isColimit
        (isColimitOfPreserves (forget CommRingCat) (colimit.isColimit F))
        (y : ((colimit F : CommRingCat) : Type v))
      change (ι i).hom x = (y : ((colimit F : CommRingCat) : Type v)) at hx
      have hxq : x ∈ (q i).primeCompl := by
        change (ι i).hom x ∉ p
        rw [hx]
        exact y.property
      rw [← hx, hf]
      exact (IsLocalization.map_units (R := F.obj i) (Localization.AtPrime (q i)) ⟨x, hxq⟩).map
        (s.ι.app i).hom
    refine ⟨{
      desc := fun s ↦ CommRingCat.ofHom
        (IsLocalization.lift (S := Localization.AtPrime p) (hu s))
      fac := ?_
      uniq := ?_ }⟩
    · intro s i
      ext1
      apply IsLocalization.ringHom_ext (q i).primeCompl
      ext x
      change IsLocalization.lift (hu s) ((κ i).hom (algebraMap _ _ x)) =
        (s.ι.app i).hom (algebraMap _ _ x)
      rw [hκ, IsLocalization.lift_eq, hf]
    · intro s m hm
      ext1
      apply IsLocalization.ringHom_ext p.primeCompl
      have hm' : CommRingCat.ofHom
          (m.hom.comp (algebraMap ((colimit F : CommRingCat) : Type v)
            (Localization.AtPrime p))) = f s := by
        apply colimit.hom_ext
        intro i
        ext x
        change m.hom (algebraMap _ _ ((ι i).hom x)) = (f s).hom ((ι i).hom x)
        rw [hf, ← hκ]
        exact ConcreteCategory.congr_hom (hm i) (algebraMap _ _ x)
      ext x
      change m.hom (algebraMap _ _ x) = IsLocalization.lift (hu s) (algebraMap _ _ x)
      rw [IsLocalization.lift_eq]
      exact ConcreteCategory.congr_hom hm' x

end AlgebraicGeometry
