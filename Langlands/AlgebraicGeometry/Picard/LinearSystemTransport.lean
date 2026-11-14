import Langlands.AlgebraicGeometry.Picard.LinearSystemUniversality

/-! # Transporting universal families along open immersions of the base

Let `a : S' ⟶ S` be an open immersion and `π : Y ×_S S' ⟶ S'` the base change of `g : Y ⟶ S`.
A universal family for the linear system of the pulled-back class over all tests of `S'` gives a
universal family for `g` over the open image of `a`: for a test `t = u ≫ a` the two fibre
products `Y ×_S T` and `(Y ×_S S') ×_{S'} T` are canonically isomorphic, compatibly with the
projections. -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.LinearSystemGluing

open PicardHilbertPiecesReduction (mapX mapX_comp mapX_congr mapX_fst mapX_snd mapX_fst_assoc
  mapX_snd_assoc dcl dcl_congr pb_comp_apply pb_iso_inv_hom pb_mapX_fst)

variable {S S' Y : Scheme.{u}} (g : Y ⟶ S) (a : S' ⟶ S)

section Comparison

variable {T : Scheme.{u}} (u : T ⟶ S') (t : T ⟶ S) (hu : u ≫ a = t)

/-- The comparison `Y ×_S T ⟶ (Y ×_S S') ×_{S'} T`. -/
def cmpψ : pullback g t ⟶ pullback (pullback.snd g a) u :=
  pullback.lift (pullback.lift (pullback.fst g t) (pullback.snd g t ≫ u)
    (by rw [pullback.condition, ← hu, Category.assoc])) (pullback.snd g t)
    (pullback.lift_snd _ _ _)

/-- The comparison `(Y ×_S S') ×_{S'} T ⟶ Y ×_S T`. -/
def cmpχ : pullback (pullback.snd g a) u ⟶ pullback g t :=
  pullback.lift (pullback.fst (pullback.snd g a) u ≫ pullback.fst g a)
    (pullback.snd (pullback.snd g a) u) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
        Category.assoc, hu])

@[reassoc]
lemma cmpψ_fst_fst : cmpψ g a u t hu ≫ pullback.fst (pullback.snd g a) u ≫ pullback.fst g a =
    pullback.fst g t := by
  rw [cmpψ, pullback.lift_fst_assoc, pullback.lift_fst]

@[reassoc]
lemma cmpψ_snd : cmpψ g a u t hu ≫ pullback.snd (pullback.snd g a) u = pullback.snd g t :=
  pullback.lift_snd _ _ _

@[reassoc]
lemma cmpχ_fst : cmpχ g a u t hu ≫ pullback.fst g t =
    pullback.fst (pullback.snd g a) u ≫ pullback.fst g a :=
  pullback.lift_fst _ _ _

@[reassoc]
lemma cmpχ_snd : cmpχ g a u t hu ≫ pullback.snd g t = pullback.snd (pullback.snd g a) u :=
  pullback.lift_snd _ _ _

lemma cmpψ_cmpχ : cmpψ g a u t hu ≫ cmpχ g a u t hu = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, cmpχ_fst, cmpψ_fst_fst, Category.id_comp]
  · rw [Category.assoc, cmpχ_snd, cmpψ_snd, Category.id_comp]

lemma cmpχ_cmpψ : cmpχ g a u t hu ≫ cmpψ g a u t hu = 𝟙 _ := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, cmpψ_fst_fst, cmpχ_fst, Category.id_comp]
    · rw [Category.assoc, Category.assoc, cmpψ, pullback.lift_fst_assoc, pullback.lift_snd,
        ← Category.assoc, cmpχ_snd, Category.id_comp, ← pullback.condition]
  · rw [Category.assoc, cmpψ_snd, cmpχ_snd, Category.id_comp]

instance : IsIso (cmpχ g a u t hu) := ⟨cmpψ g a u t hu, cmpχ_cmpψ g a u t hu, cmpψ_cmpχ g a u t hu⟩

instance : IsIso (cmpψ g a u t hu) := ⟨cmpχ g a u t hu, cmpψ_cmpχ g a u t hu, cmpχ_cmpψ g a u t hu⟩

end Comparison

variable {g a} {m : Group Y}

/-- Divisors of the linear system of `g` over `t = u ≫ a` give divisors of the base change. -/
lemma LS.comap_cmpχ {T : Scheme.{u}} {u : T ⟶ S'} {t : T ⟶ S} (hu : u ≫ a = t)
    {E : (pullback g t).IdealSheafData} (hE : LS g m t E) :
    LS (pullback.snd g a) (Group.pullback (pullback.fst g a) m) u
      (E.comap (cmpχ g a u t hu)) := by
  obtain ⟨hE, n, hn⟩ := hE
  obtain ⟨h1, hd1⟩ := PicardHilbertPiecesReduction.flat_comap (cmpχ g a u t hu)
    (pullback.snd g t) E hE
  rw [cmpχ_snd] at h1
  refine ⟨h1, n, ?_⟩
  rw [show dcl (E.comap (cmpχ g a u t hu)) h1.1 = dcl (E.comap (cmpχ g a u t hu)) _ from rfl,
    hd1, hn, map_add, ← pb_comp_apply, ← pb_comp_apply, cmpχ_fst, cmpχ_snd, pb_comp_apply]

/-- Divisors of the linear system of the base change give divisors of the linear system of `g`. -/
lemma LS.comap_cmpψ {T : Scheme.{u}} {u : T ⟶ S'} {t : T ⟶ S} (hu : u ≫ a = t)
    {E : (pullback (pullback.snd g a) u).IdealSheafData}
    (hE : LS (pullback.snd g a) (Group.pullback (pullback.fst g a) m) u E) :
    LS g m t (E.comap (cmpψ g a u t hu)) := by
  obtain ⟨hE, n, hn⟩ := hE
  obtain ⟨h1, hd1⟩ := PicardHilbertPiecesReduction.flat_comap (cmpψ g a u t hu)
    (pullback.snd (pullback.snd g a) u) E hE
  rw [cmpψ_snd] at h1
  refine ⟨h1, n, ?_⟩
  rw [show dcl (E.comap (cmpψ g a u t hu)) h1.1 = dcl (E.comap (cmpψ g a u t hu)) _ from rfl,
    hd1, hn, map_add, ← pb_comp_apply, ← pb_comp_apply, ← pb_comp_apply, Category.assoc,
    cmpψ_fst_fst, cmpψ_snd]

lemma mapX_cmpψ {P T : Scheme.{u}} {l' : P ⟶ S'} {u : T ⟶ S'} {t : T ⟶ S} (hu : u ≫ a = t)
    (k : T ⟶ P) (hk' : k ≫ l' = u) (hk : k ≫ l' ≫ a = t) :
    mapX g k hk ≫ cmpψ g a l' (l' ≫ a) rfl =
      cmpψ g a u t hu ≫ mapX (pullback.snd g a) k hk' := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, cmpψ_fst_fst, mapX_fst, Category.assoc,
        Category.assoc, mapX_fst_assoc, cmpψ_fst_fst]
    · rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc, mapX_fst_assoc,
        cmpψ, cmpψ, pullback.lift_fst_assoc, pullback.lift_snd, pullback.lift_fst_assoc,
        pullback.lift_snd, ← Category.assoc, mapX_snd, Category.assoc, hk']
  · rw [Category.assoc, Category.assoc, cmpψ_snd, mapX_snd, mapX_snd, ← Category.assoc,
      cmpψ_snd]

/-- **Transport of universality along an open immersion of the base.** -/
theorem IsUniversalOn.transport [IsOpenImmersion a] {P : Scheme.{u}} {l' : P ⟶ S'}
    {W' : (pullback (pullback.snd g a) l').IdealSheafData}
    (hU : IsUniversalOn (pullback.snd g a) (Group.pullback (pullback.fst g a) m) ⊤ l' W') :
    IsUniversalOn g m a.opensRange (l' ≫ a) (W'.comap (cmpψ g a l' (l' ≫ a) rfl)) where
  range_le := by
    rintro _ ⟨x, rfl⟩
    exact ⟨l' x, (Scheme.Hom.comp_apply _ _ _).symm⟩
  ls := hU.ls.comap_cmpψ rfl
  exists_point T _ t ht E hE := by
    have hr : Set.range t ⊆ Set.range a := by
      intro x hx
      exact ht hx
    let u := IsOpenImmersion.lift a t hr
    have hu : u ≫ a = t := IsOpenImmersion.lift_fac _ _ _
    obtain ⟨k, hk', hkE⟩ := hU.exists_point T u (fun _ _ => trivial) _ (hE.comap_cmpχ hu)
    have hk : k ≫ l' ≫ a = t := by rw [← Category.assoc, hk', hu]
    refine ⟨k, hk, ?_⟩
    rw [← Scheme.IdealSheafData.comap_comp, mapX_cmpψ hu k hk' hk,
      Scheme.IdealSheafData.comap_comp, hkE, ← Scheme.IdealSheafData.comap_comp, cmpψ_cmpχ,
      Scheme.IdealSheafData.comap_id]
  eq_of_comap_eq T _ t k₁ k₂ hk₁ hk₂ h := by
    have hu : (k₁ ≫ l') ≫ a = t := by rw [Category.assoc, hk₁]
    have hk₂' : k₂ ≫ l' = k₁ ≫ l' := by
      rw [← cancel_mono a, Category.assoc, Category.assoc, hk₁, hk₂]
    refine hU.eq_of_comap_eq T (k₁ ≫ l') k₁ k₂ rfl hk₂' ?_
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      mapX_cmpψ hu k₁ rfl hk₁, mapX_cmpψ hu k₂ hk₂' hk₂] at h
    rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp] at h
    have key : ∀ I : (pullback (pullback.snd g a) (k₁ ≫ l')).IdealSheafData,
        (I.comap (cmpψ g a (k₁ ≫ l') t hu)).comap (cmpχ g a (k₁ ≫ l') t hu) = I := by
      intro I
      rw [← Scheme.IdealSheafData.comap_comp, cmpχ_cmpψ, Scheme.IdealSheafData.comap_id]
    rw [← key (W'.comap (mapX (pullback.snd g a) k₁ rfl)),
      ← key (W'.comap (mapX (pullback.snd g a) k₂ hk₂')), h]

end Langlands.AlgebraicGeometry.Picard.LinearSystemGluing
