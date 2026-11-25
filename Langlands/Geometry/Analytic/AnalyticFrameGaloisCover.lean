import Langlands.Geometry.Analytic.AnalyticDistinctFrames
import Langlands.Geometry.Analytic.AnalyticGaloisGeometricFibres
import Langlands.Geometry.Analytic.AnalyticOpenBaseChange
import Langlands.Geometry.Analytic.ContinuousDomainEmbeddings
import Langlands.Geometry.Analytic.EtaleDomainTargetCancellation
import Langlands.Geometry.Analytic.EtaleOpenDomains.Proof

/-! # Galois covers from full finite frames -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation.CompactAnalyticFibrePower

open _root_.CategoryTheory _root_.CategoryTheory.Limits Set Topology TopologicalSpace
open AnalyticOpenBaseChange (baseInclusion projection)

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {Y X R : LocalizedCategory.{u, v, v} (K := K)} {p : Y ⟶ X} {s t : R ⟶ Y}
  {n : ℕ} (P : CompactAnalyticFibrePower.{u, v, u} p n) (h : IsPullback s t p p)
  (hY : IsCompactSpace Y) (hp : quasiEtale p) (U : Opens (localizedSpaceFunctor.obj X))

/-- The domain of distinct ordered frames over an open of the base. -/
def frameDomain : (presentationOf P.obj).AnalyticDomain :=
  (presentationOf P.obj).openDomain
    (P.distinctLocus h ∩ localizedSpaceFunctor.map P.base ⁻¹' (U : Set (localizedSpaceFunctor.obj X)))
    ((P.isDistinguishedOpen_distinctLocus h hY hp).1.inter
      (U.isOpen.preimage (localizedSpaceFunctor.map P.base).hom.continuous))

local notation "D" => P.frameDomain h hY hp U
local notation "ι" => domainι P.obj D

/-- The structure map of distinct frames over a base open. -/
def frameMap : domainObj P.obj D ⟶ AnalyticOpenBaseChange.base U :=
  domainRestrict D ((presentationOf X).openDomain (U : Set (localizedSpaceFunctor.obj X)) U.isOpen)
    P.base (fun _ hz => hz.2)

@[reassoc (attr := simp)]
theorem frameMap_comp : P.frameMap h hY hp U ≫ baseInclusion U = ι ≫ P.base :=
  domainRestrict_comp _ _ _ _

private theorem isInvariant_frameDomain : IsInvariantDomain (analyticActionOfAut P.permutations) D := by
  intro σ y hy
  change localizedSpaceFunctor.obj P.obj at y
  have hbase := congrArg (fun a : P.obj ⟶ X => localizedSpaceFunctor.map a y) (P.permutations_base σ)
  simp only [Functor.map_comp, TopCat.comp_app] at hbase
  exact ⟨P.permutations_mem_distinctLocus h σ hy.1,
    (congrArg (fun b : localizedSpaceFunctor.obj X => b ∈ U) hbase).mpr hy.2⟩

private def frameDeck : Equiv.Perm (Fin (n + 1)) →* Aut (domainObj P.obj D) :=
  (invariantDomainAction (analyticActionOfAut P.permutations) D (P.isInvariant_frameDomain h hY hp U)).ρAut

@[reassoc]
private theorem frameDeck_comp (σ : Equiv.Perm (Fin (n + 1))) :
    (P.frameDeck h hY hp U σ).asIso.hom ≫ ι = ι ≫ (P.permutations σ).asIso.hom :=
  (invariantDomainInclusion _ _ (P.isInvariant_frameDomain h hY hp U)).comm σ

private theorem frameDeck_over (σ : Equiv.Perm (Fin (n + 1))) :
    (P.frameDeck h hY hp U σ).asIso.hom ≫ P.frameMap h hY hp U = P.frameMap h hY hp U := by
  apply (cancel_mono (baseInclusion U)).mp
  rw [Category.assoc, P.frameMap_comp, P.frameDeck_comp_assoc, P.permutations_base]

private theorem etale_frameMap (hU : etale (projection U P.base)) : etale (P.frameMap h hY hp U) := by
  let E := AnalyticOpenBaseChange.domain U P.base
  have hDE : D ≤ E := fun _ hz => hz.2
  let j : domainObj P.obj D ⟶ domainObj P.obj E := domainOrderMap hDE
  have hj : j ≫ domainι P.obj E = ι := domainOrderMap_comp_inclusion hDE
  have hje : etale j := by
    apply etale_of_comp_domainι E
    rw [hj]
    exact etaleOpenDomainStatement P.obj _ ((P.isDistinguishedOpen_distinctLocus h hY hp).1.inter
      (U.isOpen.preimage (localizedSpaceFunctor.map P.base).hom.continuous))
  have heq : P.frameMap h hY hp U = j ≫ projection U P.base := by
    apply (cancel_mono (baseInclusion U)).mp
    rw [P.frameMap_comp, Category.assoc, AnalyticOpenBaseChange.projection_comp, ← Category.assoc, hj]
  rw [heq]
  exact etale_comp hje hU

private theorem injective_fin_cons {A : Type*} {m : ℕ} (a : A) (q : Fin m → A)
    (hq : Function.Injective q) (h : a ∉ range q) : Function.Injective (Fin.cases a q) := by
  intro i j e
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => rfl
    | succ j => exact (h ⟨j, e.symm⟩).elim
  | succ i =>
    cases j using Fin.cases with
    | zero => exact (h ⟨i, e⟩).elim
    | succ j => exact congrArg Fin.succ (hq e)

section FieldPoints

variable {L : Type u} [NormedField L] [NormedAlgebra K L] [IsUltrametricDist L]
  [CompleteSpace L] [IsAlgClosed L]

local notation "Φ" => localizedFieldPointFunctor (K := K) L
local notation "πτ" => localizedFieldPointProjection (K := K) L

/-- A frame's coordinate tuple, viewed in the geometric fibre of the original map. -/
def fieldFibreTuple (x : (Φ).obj P.obj) (i : Fin (n + 1)) :
    {y : (Φ).obj Y // (Φ).map p y = (Φ).map P.base x} :=
  ⟨(Φ).map (P.coord i) x, by rw [← CategoryTheory.Functor.map_comp_apply, P.coord_base]⟩

private theorem bijective_fieldFibreTuple
    (Q : CompactAnalyticFibrePower.{u, v, u} p (n + 1))
    (hlarge : ∀ z ∈ Q.distinctLocus h, localizedSpaceFunctor.map Q.base z ∉ U)
    (x : (Φ).obj P.obj) (hx : ((πτ).app P.obj x).down ∈ (D).carrier) :
    Function.Bijective (P.fieldFibreTuple x) := by
  have hinj : Function.Injective (fun i => (Φ).map (P.coord i) x) :=
    (P.mem_distinctLocus_iff_fieldPoint_injective h hY hp L x).mp hx.1
  refine ⟨fun _ _ he => hinj (congrArg Subtype.val he), ?_⟩
  intro y
  by_contra hmany
  let q : Fin (n + 1 + 1) → (Φ).obj Y := Fin.cases y.val (fun i => (Φ).map (P.coord i) x)
  have hq : ∀ i, (Φ).map p (q i) = (Φ).map P.base x := by
    intro i
    cases i using Fin.cases with
    | zero => exact y.property
    | succ i => exact (P.fieldFibreTuple x i).property
  obtain ⟨w, hw⟩ := Q.exists_fieldPoint_lift L ((Φ).map P.base x) q hq
  have hwinj : Function.Injective (fun i => (Φ).map (Q.coord i) w) := by
    have hconst : (fun i => (Φ).map (Q.coord i) w) = q := funext hw
    rw [hconst]
    apply injective_fin_cons _ _ hinj
    rintro ⟨i, hi⟩
    exact hmany ⟨i, Subtype.ext hi⟩
  have hwd := (Q.mem_distinctLocus_iff_fieldPoint_injective h hY hp L w).mpr hwinj
  have hwbase : (Φ).map Q.base w = (Φ).map P.base x := by
    rw [← Q.coord_base 0, CategoryTheory.Functor.map_comp_apply, hw]
    exact hq 0
  have heq := congrArg (fun a => ((πτ).app X a).down) hwbase
  rw [localizedFieldPointProjection_map_down, localizedFieldPointProjection_map_down] at heq
  exact hlarge _ hwd ((congrArg (fun z : localizedSpaceFunctor.obj X => z ∈ U) heq).mpr hx.2)

private theorem simplyTransitive_frameDeck
    (Q : CompactAnalyticFibrePower.{u, v, u} p (n + 1))
    (hlarge : ∀ z ∈ Q.distinctLocus h, localizedSpaceFunctor.map Q.base z ∉ U)
    (a b : (Φ).obj (domainObj P.obj D))
    (hab : (Φ).map (P.frameMap h hY hp U) a = (Φ).map (P.frameMap h hY hp U) b) :
    ∃! σ : Equiv.Perm (Fin (n + 1)), (Φ).map (P.frameDeck h hY hp U σ).asIso.hom a = b := by
  let a' := (Φ).map ι a
  let b' := (Φ).map ι b
  have hD (q : (Φ).obj (domainObj P.obj D)) : ((πτ).app P.obj ((Φ).map ι q)).down ∈ (D).carrier := by
    rw [localizedFieldPointProjection_map_down, domainι_apply]
    exact (((πτ).app (domainObj P.obj D) q).down).property
  have hbase' (q : (Φ).obj (domainObj P.obj D)) :
      (Φ).map P.base ((Φ).map ι q) =
        (Φ).map (baseInclusion U) ((Φ).map (P.frameMap h hY hp U) q) := by
    rw [← CategoryTheory.Functor.map_comp_apply, ← CategoryTheory.Functor.map_comp_apply,
      P.frameMap_comp]
  have hbbase : (Φ).map P.base a' = (Φ).map P.base b' :=
    (hbase' a).trans ((congrArg (fun z => (Φ).map (baseInclusion U) z) hab).trans (hbase' b).symm)
  let eA := Equiv.ofBijective (P.fieldFibreTuple a') (P.bijective_fieldFibreTuple h hY hp U Q hlarge a' (hD a))
  let fB (i : Fin (n + 1)) : {y : (Φ).obj Y // (Φ).map p y = (Φ).map P.base a'} :=
    ⟨(Φ).map (P.coord i) b', (P.fieldFibreTuple b' i).property.trans hbbase.symm⟩
  have hb' := P.bijective_fieldFibreTuple h hY hp U Q hlarge b' (hD b)
  have hbBij : Function.Bijective fB := by
    constructor
    · intro i j e
      have he : (fB i).val = (fB j).val := congrArg Subtype.val e
      exact hb'.1 (Subtype.ext he)
    · intro y
      obtain ⟨i, hi⟩ := hb'.2 ⟨y.val, y.property.trans hbbase⟩
      have he : (P.fieldFibreTuple b' i).val = y.val := congrArg Subtype.val hi
      exact ⟨i, Subtype.ext he⟩
  let eB := Equiv.ofBijective fB hbBij
  let σ : Equiv.Perm (Fin (n + 1)) := eA.trans eB.symm
  have hσ (i : Fin (n + 1)) : (Φ).map (P.coord (σ.symm i)) a' = (Φ).map (P.coord i) b' := by
    have he : eA (σ.symm i) = eB i := eA.apply_symm_apply (eB i)
    exact congrArg Subtype.val he
  have hcoord (τ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) :
      (Φ).map (P.coord i) ((Φ).map ι ((Φ).map (P.frameDeck h hY hp U τ).asIso.hom a)) =
        (Φ).map (P.coord (τ.symm i)) a' := by
    have hperm : (Φ).map ι ((Φ).map (P.frameDeck h hY hp U τ).asIso.hom a) =
        (Φ).map (P.permutations τ).asIso.hom a' := by
      rw [← CategoryTheory.Functor.map_comp_apply, P.frameDeck_comp,
        CategoryTheory.Functor.map_comp_apply]
    rw [hperm, ← CategoryTheory.Functor.map_comp_apply, P.permutations_coord]
  refine ⟨σ, ?_, ?_⟩
  · apply localizedFieldPoint_map_domainι_injective D
    exact P.fieldPoint_ext L (fun i => (hcoord σ i).trans (hσ i))
  · intro τ hτ
    have he : τ.symm = σ.symm := by
      apply Equiv.ext
      intro i
      have hc := hcoord τ i
      rw [hτ] at hc
      exact eA.injective (Subtype.ext (hc.symm.trans (hσ i).symm))
    exact congrArg Equiv.symm he

end FieldPoints

/-- Where there is a distinct frame of length `n + 1` at every base point
and no frame of length `n + 2`, the ordered frames form a Galois covering. -/
def frameGaloisCover (Q : CompactAnalyticFibrePower.{u, v, u} p (n + 1))
    (hU : etale (projection U P.base))
    (hsmall : ∀ x ∈ U, ∃ z ∈ P.distinctLocus h, localizedSpaceFunctor.map P.base z = x)
    (hlarge : ∀ z ∈ Q.distinctLocus h, localizedSpaceFunctor.map Q.base z ∉ U) :
    AnalyticGaloisCover (Equiv.Perm (Fin (n + 1))) (P.frameMap h hY hp U) := by
  have hsurj : Function.Surjective (localizedSpaceFunctor.map (P.frameMap h hY hp U)) := by
    intro x
    obtain ⟨z, hzd, hz⟩ := hsmall x.val x.property
    have hzU : localizedSpaceFunctor.map P.base z ∈ U := (congrArg (· ∈ U) hz).mpr x.property
    let z' : localizedSpaceFunctor.obj (domainObj P.obj D) := ⟨z, hzd, hzU⟩
    have he := congrArg (fun f => localizedSpaceFunctor.map f z') (P.frameMap_comp h hY hp U)
    simp only [Functor.map_comp, TopCat.comp_app, domainι_apply] at he
    exact ⟨z', Subtype.ext (he.trans hz)⟩
  exact AnalyticGaloisCover.of_geometricFibres (P.etale_frameMap h hY hp U hU) hsurj
    (P.frameDeck h hY hp U) (P.frameDeck_over h hY hp U)
    (fun L _ _ _ _ _ a b hab => P.simplyTransitive_frameDeck h hY hp U Q hlarge (L := L) a b hab)

end Langlands.Analytic.SaturatedAtlasPresentation.CompactAnalyticFibrePower
