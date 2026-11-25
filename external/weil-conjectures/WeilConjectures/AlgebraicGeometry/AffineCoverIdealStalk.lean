/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Data.Fintype.Order

/-!
# Descent of compatible affine ideals to a stalk

Source: Stacks Project, Tags 01HR, 01I6, and 01LA; Tag 0BVH.
-/

@[expose] public section

universe u v
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Stalkwise membership on a principal open can be cleared by one power. -/
private theorem exists_pow_mul_mem_of_germ_mem
    {Y : Scheme.{u}} (U : Y.affineOpens) (I : Ideal Γ(Y, U.1))
    (a f : Γ(Y, U.1))
    (h : ∀ (y : Y) (hy : y ∈ Y.basicOpen f),
      Y.presheaf.germ U.1 y (Y.basicOpen_le f hy) a ∈
        I.map (Y.presheaf.germ U.1 y (Y.basicOpen_le f hy)).hom) :
    ∃ n : ℕ, f ^ n * a ∈ I := by
  let := U.2.isLocalization_basicOpen f
  have hm : algebraMap Γ(Y, U.1) Γ(Y, Y.basicOpen f) a ∈
      I.map (algebraMap Γ(Y, U.1) Γ(Y, Y.basicOpen f)) := by
    apply (Y.affineBasicOpen f).2.mem_ideal_iff.mpr
    intro y hy
    change Y.presheaf.germ (Y.basicOpen f) y hy
      (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op a) ∈
        (I.map (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom).map
          (Y.presheaf.germ (Y.basicOpen f) y hy).hom
    simpa only [Ideal.map_map, ← CommRingCat.hom_comp,
      TopCat.Presheaf.germ_res, TopCat.Presheaf.germ_res_apply] using h y hy
  obtain ⟨m, hm, ha⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers f)
      Γ(Y, Y.basicOpen f) I a).mp hm
  obtain ⟨n, rfl⟩ := hm
  exact ⟨n, ha⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- Compatible ideals on finitely many principal opens have the expected stalks.
The principal opens need not cover the ambient affine open. -/
private theorem finiteBasicIdeal_map_germ
    {Y : Scheme.{u}} (U : Y.affineOpens) (s : Finset Γ(Y, U.1))
    (K : ∀ f : s, Ideal Γ(Y, Y.basicOpen f.1))
    (hcompat : ∀ (f g : s) (y : Y) (hf : y ∈ Y.basicOpen f.1)
      (hg : y ∈ Y.basicOpen g.1),
      (K f).map (Y.presheaf.germ (Y.basicOpen f.1) y hf).hom =
        (K g).map (Y.presheaf.germ (Y.basicOpen g.1) y hg).hom)
    (f : s) (y : Y) (hy : y ∈ Y.basicOpen f.1) :
    (⨅ g : s, (K g).comap
      (Y.presheaf.map (homOfLE (Y.basicOpen_le g.1)).op).hom).map
        (Y.presheaf.germ U.1 y (Y.basicOpen_le f.1 hy)).hom =
      (K f).map (Y.presheaf.germ (Y.basicOpen f.1) y hy).hom := by
  classical
  let r (g : s) := (Y.presheaf.map (homOfLE (Y.basicOpen_le g.1)).op).hom
  let L : Ideal Γ(Y, U.1) := ⨅ g : s, (K g).comap (r g)
  change L.map _ = _
  apply le_antisymm
  · calc
      L.map (Y.presheaf.germ U.1 y (Y.basicOpen_le f.1 hy)).hom ≤
          ((K f).comap (r f)).map
            (Y.presheaf.germ U.1 y (Y.basicOpen_le f.1 hy)).hom :=
        Ideal.map_mono (iInf_le _ f)
      _ = (((K f).comap (r f)).map (r f)).map
          (Y.presheaf.germ (Y.basicOpen f.1) y hy).hom := by
        rw [Ideal.map_map, ← CommRingCat.hom_comp, TopCat.Presheaf.germ_res]
      _ ≤ (K f).map (Y.presheaf.germ (Y.basicOpen f.1) y hy).hom :=
        Ideal.map_mono Ideal.map_comap_le
  · let := U.2.isLocalization_basicOpen f.1
    have hK : K f = ((K f).comap (r f)).map (r f) :=
      (IsLocalization.map_under (Submonoid.powers f.1) Γ(Y, Y.basicOpen f.1) (K f)).symm
    rw [hK, Ideal.map_map, ← CommRingCat.hom_comp, TopCat.Presheaf.germ_res]
    refine Ideal.map_le_iff_le_comap.mpr ?_
    intro a ha
    -- Clear the denominator on each chart, then choose a common exponent.
    have hex (g : s) : ∃ n : ℕ, (r g f.1) ^ n * r g a ∈ K g := by
      apply exists_pow_mul_mem_of_germ_mem (Y.affineBasicOpen g.1) (K g)
      intro z hz
      change z ∈ Y.basicOpen
        (Y.presheaf.map (homOfLE (Y.basicOpen_le g.1)).op f.1) at hz
      rw [Scheme.basicOpen_res] at hz
      have hz' : z ∈ Y.basicOpen g.1 ⊓ Y.basicOpen f.1 := hz
      have hm := Ideal.mem_map_of_mem
        (Y.presheaf.germ (Y.basicOpen f.1) z hz'.2).hom ha
      rw [hcompat f g z hz'.2 hz'.1] at hm
      change Y.presheaf.germ (Y.basicOpen g.1) z _
        (Y.presheaf.map (homOfLE (Y.basicOpen_le g.1)).op a) ∈ _
      change Y.presheaf.germ (Y.basicOpen f.1) z hz'.2
        (Y.presheaf.map (homOfLE (Y.basicOpen_le f.1)).op a) ∈ _ at hm
      simpa only [TopCat.Presheaf.germ_res_apply] using! hm
    choose n hn using hex
    obtain ⟨N, hN⟩ := Finite.exists_le n
    have hmem : f.1 ^ N * a ∈ L := by
      apply Ideal.mem_iInf.mpr
      intro g
      change r g (f.1 ^ N * a) ∈ K g
      rw [map_mul, map_pow]
      have hm := (K g).mul_mem_left ((r g f.1) ^ (N - n g)) (hn g)
      simpa only [← mul_assoc, ← pow_add, Nat.sub_add_cancel (hN g)] using hm
    have hm := Ideal.mem_map_of_mem
      (Y.presheaf.germ U.1 y (Y.basicOpen_le f.1 hy)).hom hmem
    rw [map_mul, map_pow] at hm
    exact (Ideal.unit_mul_mem_iff_mem _
      (((Y.mem_basicOpen f.1 y (Y.basicOpen_le f.1 hy)).mp hy).pow N)).mp hm

/-- Compatible ideals on an affine cover have the expected stalks when their
sections on the larger affine open are defined by an intersection of inverse images.

Source: Stacks Project, Tag 01HR (affine schemes, lemma-affine-sheaves), Tag 01I6
(quasi-coherent sheaves on affines, lemma-compare-constructions), and Tag 01LA
(functoriality for quasi-coherent modules, locality of quasi-coherence).
Tag 0BVH uses this construction for discriminants.
(blueprint: lem-sbc-affine-cover-ideal-stalk)

Proof: Put A_i = Gamma(V_i). Exactness of localization identifies the sheaf
associated to the inclusion J_i in A_i with a subsheaf K_i of the structure sheaf
on V_i; its stalk at z is the ideal generated by the germs of J_i. The compatibility
hypothesis says that K_i and K_j have equal stalk submodules on V_i intersect V_j.
A section of either subsheaf belongs to the other locally at every point and hence
globally by the sheaf axiom. Thus these restrictions agree as subsheaves. Their
identity identifications satisfy the cocycle condition, so sheaf gluing constructs
a subsheaf K on U restricting to every K_i. It is quasi-coherent because that
property is local. The affine tilde/global-sections equivalence therefore identifies
K with the sheaf associated to its section ideal L in Gamma(U). For a section a of
Gamma(U), membership in L is equivalent to membership of each restriction a|V_i
in J_i: the forward direction restricts K-sections, and the reverse direction glues
the local K_i-sections, whose underlying structure-sheaf sections already agree.
Consequently L is exactly the displayed inverse-image intersection. Finally the
stalk of the sheaf associated to L is its localization at z, equivalently its image
ideal under the germ map. Since K restricts to K_i, that stalk is also the image
ideal of J_i under its germ map, proving equality. This works with an arbitrary
cover and requires no exchange of localization with an infinite intersection.
The cover may be empty only when U is empty, in which case there is no point y to test.
-/
theorem affineCoverIdeal_map_germ
    {Y : Scheme.{u}} [IsLocallyNoetherian Y] (U : Y.affineOpens)
    {ι : Type v} (V : ι → Y.affineOpens) (hV : ∀ i, (V i).1 ≤ U.1)
    (J : ∀ i, Ideal Γ(Y, (V i).1))
    (hcover : ∀ y : Y, y ∈ U.1 → ∃ i, y ∈ (V i).1)
    (hcompat : ∀ i j (y : Y) (hi : y ∈ (V i).1) (hj : y ∈ (V j).1),
      (J i).map (Y.presheaf.germ (V i).1 y hi).hom =
        (J j).map (Y.presheaf.germ (V j).1 y hj).hom)
    (i : ι) (y : Y) (hy : y ∈ (V i).1) :
    (⨅ j, (J j).comap (Y.presheaf.map (homOfLE (hV j)).op).hom).map
        (Y.presheaf.germ U.1 y (hV i hy)).hom =
      (J i).map (Y.presheaf.germ (V i).1 y hy).hom := by
  classical
  -- Refine the original cover to a finite principal cover of U.
  let T : Set Γ(Y, U.1) := {f | ∃ j, Y.basicOpen f ≤ (V j).1}
  have hT : Ideal.span T = ⊤ := by
    apply U.2.self_le_iSup_basicOpen_iff.mp
    intro z hz
    obtain ⟨j, hj⟩ := hcover z hz
    obtain ⟨f, hf, hzf⟩ := U.2.exists_basicOpen_le ⟨z, hj⟩ hz
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, j, hf⟩, hzf⟩
  obtain ⟨s, hs, hspan⟩ := Ideal.span_eq_top_iff_finite T |>.mp hT
  have hscover : U.1 ≤ ⨆ f : s, Y.basicOpen f.1 :=
    U.2.self_le_iSup_basicOpen_iff.mpr hspan
  have hchoice (f : s) : ∃ j, Y.basicOpen f.1 ≤ (V j).1 := hs f.2
  choose k hk using hchoice
  let K (f : s) : Ideal Γ(Y, Y.basicOpen f.1) :=
    (J (k f)).map (Y.presheaf.map (homOfLE (hk f)).op).hom
  have hKgerm (f : s) (z : Y) (hz : z ∈ Y.basicOpen f.1) :
      (K f).map (Y.presheaf.germ (Y.basicOpen f.1) z hz).hom =
        (J (k f)).map (Y.presheaf.germ (V (k f)).1 z (hk f hz)).hom := by
    dsimp only [K]
    rw [Ideal.map_map, ← CommRingCat.hom_comp, TopCat.Presheaf.germ_res]
  have hKcompat (f g : s) (z : Y) (hf : z ∈ Y.basicOpen f.1)
      (hg : z ∈ Y.basicOpen g.1) :
      (K f).map (Y.presheaf.germ (Y.basicOpen f.1) z hf).hom =
        (K g).map (Y.presheaf.germ (Y.basicOpen g.1) z hg).hom := by
    rw [hKgerm f z hf, hKgerm g z hg]
    exact hcompat (k f) (k g) z (hk f hf) (hk g hg)
  let L : Ideal Γ(Y, U.1) := ⨅ f : s, (K f).comap
    (Y.presheaf.map (homOfLE (Y.basicOpen_le f.1)).op).hom
  -- The stalk criterion identifies the finite and original intersection ideals.
  have hL : L = ⨅ j, (J j).comap (Y.presheaf.map (homOfLE (hV j)).op).hom := by
    apply le_antisymm
    · refine le_iInf fun j ↦ ?_
      intro a ha
      apply (V j).2.mem_ideal_iff.mpr
      intro z hz
      obtain ⟨f, hf⟩ := TopologicalSpace.Opens.mem_iSup.mp (hscover (hV j hz))
      have haf : Y.presheaf.map (homOfLE (Y.basicOpen_le f.1)).op a ∈ K f :=
        Ideal.mem_iInf.mp ha f
      have hm := Ideal.mem_map_of_mem
        (Y.presheaf.germ (Y.basicOpen f.1) z hf).hom haf
      rw [hKgerm f z hf, hcompat (k f) j z (hk f hf) hz] at hm
      simpa only [TopCat.Presheaf.germ_res_apply] using! hm
    · intro a ha
      apply Ideal.mem_iInf.mpr
      intro f
      have haj : Y.presheaf.map (homOfLE (hV (k f))).op a ∈ J (k f) :=
        Ideal.mem_iInf.mp ha (k f)
      have hm := Ideal.mem_map_of_mem
        (Y.presheaf.map (homOfLE (hk f)).op).hom haj
      change Y.presheaf.map (homOfLE (Y.basicOpen_le f.1)).op a ∈ K f
      change Y.presheaf.map (homOfLE (hk f)).op
        (Y.presheaf.map (homOfLE (hV (k f))).op a) ∈ K f at hm
      have he : (homOfLE (hV (k f))).op ≫ (homOfLE (hk f)).op =
          (homOfLE (Y.basicOpen_le f.1)).op := Subsingleton.elim _ _
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, he] at hm
      exact hm
  obtain ⟨f, hf⟩ := TopologicalSpace.Opens.mem_iSup.mp (hscover (hV i hy))
  rw [← hL]
  calc
    L.map (Y.presheaf.germ U.1 y (hV i hy)).hom =
        (K f).map (Y.presheaf.germ (Y.basicOpen f.1) y hf).hom :=
      finiteBasicIdeal_map_germ U s K hKcompat f y hf
    _ = (J (k f)).map (Y.presheaf.germ (V (k f)).1 y (hk f hf)).hom :=
      hKgerm f y hf
    _ = (J i).map (Y.presheaf.germ (V i).1 y hy).hom :=
      hcompat (k f) i y (hk f hf) hy

end AlgebraicGeometry.Scheme
