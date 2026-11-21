import Langlands.Geometry.Analytic.LocalizedPullbackCompactPreimages
import Langlands.Geometry.Analytic.QuasiEtaleCommonProduct
import Langlands.Geometry.Analytic.QuasiEtaleFieldPointPullback

/-! # Finite nonempty fibre powers of compact quasi-étale maps -/

noncomputable section

universe u v uL

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {Y X : LocalizedCategory.{u, v, v} (K := K)} {p : Y ⟶ X}

private theorem isCompactSpace_of_pullback_in_hausdorff_subset
    {A B P : LocalizedCategory.{u, v, v} (K := K)}
    {f : A ⟶ X} {g : B ⟶ X} {a : P ⟶ A} {b : P ⟶ B}
    (h : IsPullback a b f g) (hf : quasiEtale f) (hA : IsCompactSpace A) (hB : IsCompactSpace B)
    (S : Set (localizedSpaceFunctor.obj X)) [T2Space S]
    (hS₁ : ∀ z, localizedSpaceFunctor.map f z ∈ S)
    (hS₂ : ∀ z, localizedSpaceFunctor.map g z ∈ S) : IsCompactSpace P := by
  let : CompactSpace (localizedSpaceFunctor.obj A) := hA.1
  let : CompactSpace (localizedSpaceFunctor.obj B) := hB.1
  let : T2Space (localizedSpaceFunctor.obj A) := hA.2
  let : T2Space (localizedSpaceFunctor.obj B) := hB.2
  let T : Set (localizedSpaceFunctor.obj A × localizedSpaceFunctor.obj B) :=
    {z | localizedSpaceFunctor.map f z.1 = localizedSpaceFunctor.map g z.2}
  have hT : IsClosed T := by
    have h₁ : Continuous (fun z : localizedSpaceFunctor.obj A × localizedSpaceFunctor.obj B =>
        (⟨localizedSpaceFunctor.map f z.1, hS₁ z.1⟩ : S)) :=
      ((localizedSpaceFunctor.map f).hom.continuous.comp continuous_fst).subtype_mk _
    have h₂ : Continuous (fun z : localizedSpaceFunctor.obj A × localizedSpaceFunctor.obj B =>
        (⟨localizedSpaceFunctor.map g z.2, hS₂ z.2⟩ : S)) :=
      ((localizedSpaceFunctor.map g).hom.continuous.comp continuous_snd).subtype_mk _
    have heq : {z | (⟨localizedSpaceFunctor.map f z.1, hS₁ z.1⟩ : S) =
        ⟨localizedSpaceFunctor.map g z.2, hS₂ z.2⟩} = T := by
      ext z
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    exact heq ▸ isClosed_eq h₁ h₂
  have hcompact := hasCompactPairPreimages_of_quasiEtale h hf
  have hpre : localizedProjectionPair a b ⁻¹' T = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    change localizedSpaceFunctor.map f (localizedSpaceFunctor.map a z) =
      localizedSpaceFunctor.map g (localizedSpaceFunctor.map b z)
    have hz := congrArg (fun m : P ⟶ X => localizedSpaceFunctor.map m z) h.w
    simpa only [Functor.map_comp, TopCat.comp_app] using hz
  have hP := hcompact.2 T (isCompact_univ.of_isClosed_subset hT (subset_univ _)) (fun _ hz => hz)
  rw [hpre] at hP
  exact ⟨isCompact_univ_iff.mp hP, hcompact.1⟩

/-- A compact Hausdorff analytic `(n + 1)`-fold fibre power. Its coordinates
have the universal property on analytic arrows and on full points over
complete algebraically closed value fields. -/
structure CompactAnalyticFibrePower (p : Y ⟶ X) (n : ℕ) where
  obj : LocalizedCategory.{u, v, v} (K := K)
  base : obj ⟶ X
  coord : Fin (n + 1) → (obj ⟶ Y)
  coord_base : ∀ i, coord i ≫ p = base
  compact : IsCompactSpace obj
  quasiEtale_base : quasiEtale base
  hom_ext : ∀ {T : LocalizedCategory.{u, v, v} (K := K)} {a b : T ⟶ obj},
    (∀ i, a ≫ coord i = b ≫ coord i) → a = b
  exists_lift : ∀ {T : LocalizedCategory.{u, v, v} (K := K)} (a : T ⟶ X)
    (q : Fin (n + 1) → (T ⟶ Y)), (∀ i, q i ≫ p = a) →
    ∃ b : T ⟶ obj, ∀ i, b ≫ coord i = q i
  fieldPoint_ext : ∀ (L : Type uL) [NormedField L] [NormedAlgebra K L] [IsUltrametricDist L]
    [CompleteSpace L] [IsAlgClosed L] {a b : (localizedFieldPointFunctor L).obj obj},
    (∀ i, (localizedFieldPointFunctor L).map (coord i) a =
      (localizedFieldPointFunctor L).map (coord i) b) → a = b
  exists_fieldPoint_lift : ∀ (L : Type uL) [NormedField L] [NormedAlgebra K L] [IsUltrametricDist L]
    [CompleteSpace L] [IsAlgClosed L] (a : (localizedFieldPointFunctor L).obj X)
    (q : Fin (n + 1) → (localizedFieldPointFunctor L).obj Y),
    (∀ i, (localizedFieldPointFunctor L).map p (q i) = a) →
    ∃ b : (localizedFieldPointFunctor L).obj obj, ∀ i, (localizedFieldPointFunctor L).map (coord i) b = q i

namespace CompactAnalyticFibrePower

private def single (hp : quasiEtale p) (hY : IsCompactSpace Y) : CompactAnalyticFibrePower.{u, v, uL} p 0 where
  obj := Y
  base := p
  coord _ := 𝟙 Y
  coord_base _ := Category.id_comp _
  compact := hY
  quasiEtale_base := hp
  hom_ext h := by simpa only [Category.comp_id] using h 0
  exists_lift _ q _ := ⟨q 0, fun i => by rw [Category.comp_id, Fin.eq_zero i]⟩
  fieldPoint_ext L _ _ _ _ _ a b h := by simpa only [CategoryTheory.Functor.map_id_apply] using h 0
  exists_fieldPoint_lift L _ _ _ _ _ a q h :=
    ⟨q 0, fun i => by rw [CategoryTheory.Functor.map_id_apply, Fin.eq_zero i]⟩

variable {n : ℕ} (P : CompactAnalyticFibrePower.{u, v, uL} p n)

private def cons (hp : quasiEtale p) (hY : IsCompactSpace Y)
    (S : Set (localizedSpaceFunctor.obj X)) [T2Space S]
    (hS : ∀ z, localizedSpaceFunctor.map p z ∈ S) : CompactAnalyticFibrePower.{u, v, uL} p (n + 1) := by
  let Q := localizedQuasiEtalePullback p P.base hp
  let r := Q.1.fst
  let s := Q.1.snd
  have hQ : IsPullback r s p P.base := IsPullback.of_isLimit Q.2
  have hbase (z : localizedSpaceFunctor.obj P.obj) : localizedSpaceFunctor.map P.base z ∈ S := by
    rw [← P.coord_base 0, Functor.map_comp, TopCat.comp_app]
    exact hS _
  let : T2Space (localizedSpaceFunctor.obj Y) := hY.2
  let : T2Space (localizedSpaceFunctor.obj P.obj) := P.compact.2
  refine
    { obj := Q.1.pt
      base := s ≫ P.base
      coord := Fin.cases r (fun i => s ≫ P.coord i)
      coord_base := fun i => Fin.cases hQ.w (fun j => by
        change (s ≫ P.coord j) ≫ p = s ≫ P.base
        rw [Category.assoc, P.coord_base]) i
      compact := isCompactSpace_of_pullback_in_hausdorff_subset hQ hp hY P.compact S hS hbase
      quasiEtale_base := quasiEtale_common_of_isPullback hQ hp P.quasiEtale_base
      hom_ext := ?_
      exists_lift := ?_
      fieldPoint_ext := ?_
      exists_fieldPoint_lift := ?_ }
  · intro T a b hab
    apply hQ.hom_ext (hab 0)
    apply P.hom_ext
    intro j
    have hj := hab j.succ
    change a ≫ (s ≫ P.coord j) = b ≫ (s ≫ P.coord j) at hj
    simpa only [Category.assoc] using hj
  · intro T a q hq
    obtain ⟨b, hb⟩ := P.exists_lift a (fun i => q i.succ) (fun i => hq i.succ)
    have hbX : b ≫ P.base = a := by
      rw [← P.coord_base 0, ← Category.assoc, hb]
      exact hq (Fin.succ 0)
    obtain ⟨l, hlr, hls⟩ := hQ.exists_lift (q 0) b ((hq 0).trans hbX.symm)
    refine ⟨l, fun i => Fin.cases hlr (fun j => ?_) i⟩
    change l ≫ s ≫ P.coord j = q j.succ
    rw [← Category.assoc, hls, hb]
  · intro L _ _ _ _ _ a b hab
    let Φ := localizedFieldPointFunctor (K := K) L
    have hQΦ := localizedQuasiEtaleFieldPointPullback (L := L) r s p P.base hp hQ
    apply Types.ext_of_isPullback hQΦ (hab 0)
    apply P.fieldPoint_ext L
    intro i
    change Φ.map (P.coord i) (Φ.map s a) = Φ.map (P.coord i) (Φ.map s b)
    rw [← Φ.map_comp_apply, ← Φ.map_comp_apply]
    exact hab i.succ
  · intro L _ _ _ _ _ a q hq
    let Φ := localizedFieldPointFunctor (K := K) L
    obtain ⟨b, hb⟩ := P.exists_fieldPoint_lift L a (fun i => q i.succ) (fun i => hq i.succ)
    have hbX : Φ.map P.base b = a := by
      rw [← P.coord_base 0, Φ.map_comp_apply]
      have h := hb 0
      change Φ.map (P.coord 0) b = q (Fin.succ 0) at h
      rw [h]
      exact hq (Fin.succ 0)
    have hQΦ := localizedQuasiEtaleFieldPointPullback (L := L) r s p P.base hp hQ
    obtain ⟨l, hlr, hls⟩ := Types.exists_of_isPullback hQΦ (q 0) b ((hq 0).trans hbX.symm)
    refine ⟨l, fun i => Fin.cases hlr (fun j => ?_) i⟩
    change Φ.map (s ≫ P.coord j) l = q j.succ
    rw [Φ.map_comp_apply]
    have h : Φ.map s l = b := hls
    rw [h]
    exact hb j

/-- Construct the finite nonempty fibre powers when the compact source maps
into a Hausdorff subspace of the base. -/
def of_quasiEtale (hp : quasiEtale p) (hY : IsCompactSpace Y)
    (S : Set (localizedSpaceFunctor.obj X)) [T2Space S] (hS : ∀ z, localizedSpaceFunctor.map p z ∈ S) :
    (n : ℕ) → CompactAnalyticFibrePower.{u, v, uL} p n
  | 0 => single hp hY
  | n + 1 => (of_quasiEtale hp hY S hS n).cons hp hY S hS

/-- The map into a fibre power determined by compatible coordinates. -/
def lift {T : LocalizedCategory.{u, v, v} (K := K)} (a : T ⟶ X) (q : Fin (n + 1) → (T ⟶ Y))
    (h : ∀ i, q i ≫ p = a) : T ⟶ P.obj :=
  Classical.choose (P.exists_lift a q h)

@[reassoc (attr := simp)]
theorem lift_coord {T : LocalizedCategory.{u, v, v} (K := K)} (a : T ⟶ X)
    (q : Fin (n + 1) → (T ⟶ Y)) (h : ∀ i, q i ≫ p = a) (i : Fin (n + 1)) :
    P.lift a q h ≫ P.coord i = q i :=
  Classical.choose_spec (P.exists_lift a q h) i

@[reassoc (attr := simp)]
theorem lift_base {T : LocalizedCategory.{u, v, v} (K := K)} (a : T ⟶ X)
    (q : Fin (n + 1) → (T ⟶ Y)) (h : ∀ i, q i ≫ p = a) : P.lift a q h ≫ P.base = a := by
  rw [← P.coord_base 0, ← Category.assoc, P.lift_coord, h]

private def permute (σ : Equiv.Perm (Fin (n + 1))) : P.obj ⟶ P.obj :=
  P.lift P.base (fun i => P.coord (σ.symm i)) (fun _ => P.coord_base _)

@[reassoc]
private theorem permute_coord (σ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) :
    P.permute σ ≫ P.coord i = P.coord (σ.symm i) := P.lift_coord _ _ _ _

/-- Permuting the coordinates gives the left permutation action, with the
`i`-th coordinate of a translate read at the inverse permutation of `i`. -/
def permutations : Equiv.Perm (Fin (n + 1)) →* Aut P.obj where
  toFun σ :=
    { hom := P.permute σ
      inv := P.permute σ.symm
      hom_inv_id := by
        apply P.hom_ext
        intro i
        rw [Category.assoc, P.permute_coord, P.permute_coord, Category.id_comp,
          Equiv.symm_symm, Equiv.symm_apply_apply]
      inv_hom_id := by
        apply P.hom_ext
        intro i
        rw [Category.assoc, P.permute_coord, P.permute_coord, Category.id_comp,
          Equiv.symm_symm, Equiv.apply_symm_apply] }
  map_one' := Iso.ext (by
    apply P.hom_ext
    intro i
    change P.permute 1 ≫ P.coord i = 𝟙 _ ≫ P.coord i
    rw [P.permute_coord, Category.id_comp]
    rfl)
  map_mul' σ τ := Iso.ext (by
    apply P.hom_ext
    intro i
    change P.permute (σ * τ) ≫ P.coord i = (P.permute τ ≫ P.permute σ) ≫ P.coord i
    rw [Category.assoc, P.permute_coord, P.permute_coord, P.permute_coord]
    rfl)

@[reassoc (attr := simp)]
theorem permutations_coord (σ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) :
    (P.permutations σ).hom ≫ P.coord i = P.coord (σ.symm i) := P.permute_coord σ i

@[reassoc (attr := simp)]
theorem permutations_base (σ : Equiv.Perm (Fin (n + 1))) :
    (P.permutations σ).hom ≫ P.base = P.base :=
  P.lift_base P.base (fun i => P.coord (σ.symm i)) (fun _ => P.coord_base _)

end CompactAnalyticFibrePower

end Langlands.Analytic.SaturatedAtlasPresentation
