import Langlands.GroupScheme.HomScheme.AdmissibleDescent
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesZariskiSheafGeneral
import Mathlib.AlgebraicGeometry.Sites.BigZariski

/-! # Sheafness from effective descent of actual admissible families -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TorusSubgroupModuli

variable {S : Scheme.{u}} (G : GroupScheme S)

/-- The effective-admissibility obligation for the explicit matching subgroup. -/
def HasEffectiveAdmissibleDescent : Prop :=
  ∀ (T : Over S) (𝒰 : Scheme.OpenCover.{u} T.left)
    (F : ∀ i, AdmissibleSubgroup
      ((baseChange (SubgroupFunctor.coverObj 𝒰 i : Over S).hom).obj G)),
    IsMatchingAdmissible 𝒰 F → IsAdmissible (matchingSubgroup 𝒰 F)

/-- Compatible small sections are matching actual admissible families. -/
theorem isMatchingAdmissible_of_compatible {T : Over S}
    (𝒰 : Scheme.OpenCover.{u} T.left)
    (q : ∀ i, (smallAdmissiblePresheaf G).obj
      (op (SubgroupFunctor.coverObj 𝒰 i)))
    (hq : Presieve.Arrows.Compatible (smallAdmissiblePresheaf G)
      (fun i => SubgroupFunctor.coverMap 𝒰 i) q) :
    IsMatchingAdmissible 𝒰
      (fun i => smallAdmissibleEquiv G _ (q i)) := by
  intro i j A a b hab
  have h := congrArg (smallAdmissibleEquiv G A) (hq i j A a b hab)
  simpa only [smallAdmissibleEquiv_map] using h

/-- Effective admissibility gives unique gluing on each parameter cover. -/
theorem smallAdmissible_isSheafFor_cover (hG : HasEffectiveAdmissibleDescent G)
    (T : Over S) (𝒰 : Scheme.OpenCover.{u} T.left) :
    Presieve.IsSheafFor (smallAdmissiblePresheaf G) (Langlands.AlgebraicGeometry.Picard.openCoverOver T 𝒰).presieve₀ := by
  apply (Presieve.isSheafFor_arrows_iff _ _).mpr
  intro q hq
  let F i := smallAdmissibleEquiv G _ (q i)
  have hF : IsMatchingAdmissible 𝒰 F :=
    isMatchingAdmissible_of_compatible G 𝒰 q hq
  let H : AdmissibleSubgroup ((baseChange T.hom).obj G) :=
    ⟨matchingSubgroup 𝒰 F, hG T 𝒰 F hF⟩
  refine ⟨(smallAdmissibleEquiv G T).symm H, ?_, ?_⟩
  · intro i
    apply (smallAdmissibleEquiv G _).injective
    rw [smallAdmissibleEquiv_map, Equiv.apply_symm_apply]
    exact restrict_matchingSubgroup 𝒰 F hF _ i
  · intro q' hq'
    apply (smallAdmissibleEquiv G T).injective
    rw [Equiv.apply_symm_apply]
    apply eq_of_restrict_cover 𝒰
    intro i
    have hi := congrArg (smallAdmissibleEquiv G _) (hq' i)
    rw [smallAdmissibleEquiv_map] at hi
    exact hi.trans (restrict_matchingSubgroup 𝒰 F hF _ i).symm

private theorem total_eq_of_fibre_eq {P : (Over S)ᵒᵖ ⥤ Type u}
    (T : Over S) (x y : P.OverTotal T.left)
    (hx : x.1 = T.hom) (hy : y.1 = T.hom)
    (h : Functor.OverTotal.toFibre T x hx = Functor.OverTotal.toFibre T y hy) :
    x = y := by
  rw [← Functor.OverTotal.ofFibre_toFibre T x hx,
    ← Functor.OverTotal.ofFibre_toFibre T y hy, h]

private theorem overTotal_isSheafFor_cover
    (P : (Over S)ᵒᵖ ⥤ Type u)
    (hP : ∀ (T : Over S) (𝒱 : Scheme.OpenCover.{u} T.left),
      Presieve.IsSheafFor P (Langlands.AlgebraicGeometry.Picard.openCoverOver T 𝒱).presieve₀)
    (X : Scheme.{u}) (𝒰 : Scheme.OpenCover.{u} X) :
    Presieve.IsSheafFor P.overTotal (Presieve.ofArrows 𝒰.X 𝒰.f) := by
  apply (Presieve.isSheafFor_arrows_iff _ _).mpr
  intro q hq
  have hc (i j : 𝒰.I₀) :
      pullback.fst (𝒰.f i) (𝒰.f j) ≫ (q i).1 =
        pullback.snd (𝒰.f i) (𝒰.f j) ≫ (q j).1 :=
    congrArg (fun z => z.1) (hq i j _ _ _ pullback.condition)
  let t := 𝒰.glueMorphisms (fun i => (q i).1) hc
  have ht (i : 𝒰.I₀) : 𝒰.f i ≫ t = (q i).1 :=
    𝒰.ι_glueMorphisms _ hc i
  let T : Over S := Over.mk t
  let C (i : 𝒰.I₀) : Over S := SubgroupFunctor.coverObj (T := T) 𝒰 i
  have hb (i : 𝒰.I₀) : (q i).1 = (C i).hom := (ht i).symm
  let r (i : 𝒰.I₀) := Functor.OverTotal.toFibre (C i) (q i) (hb i)
  have hr : Presieve.Arrows.Compatible P
      (fun i => SubgroupFunctor.coverMap (T := T) 𝒰 i) r := by
    intro i j A a b hab
    have hai : (P.overTotal.map a.left.op (q i)).1 = A.hom := by
      rw [Functor.overTotal_map_fst, hb i]
      exact Over.w a
    have hbj : (P.overTotal.map b.left.op (q j)).1 = A.hom := by
      rw [Functor.overTotal_map_fst, hb j]
      exact Over.w b
    have hab' : a.left ≫ 𝒰.f i = b.left ≫ 𝒰.f j :=
      congrArg (fun f => f.left) hab
    calc
      P.map a.op (r i) =
          Functor.OverTotal.toFibre A (P.overTotal.map a.left.op (q i)) hai :=
        (Functor.OverTotal.toFibre_naturality a (q i) (hb i) hai).symm
      _ = Functor.OverTotal.toFibre A (P.overTotal.map b.left.op (q j)) hbj :=
        Functor.OverTotal.toFibre_congr A (hq i j A.left a.left b.left hab') hai hbj
      _ = P.map b.op (r j) :=
        Functor.OverTotal.toFibre_naturality b (q j) (hb j) hbj
  obtain ⟨r₀, hr₀, hur₀⟩ :=
    (Presieve.isSheafFor_arrows_iff _ _).mp
      (hP T 𝒰) r hr
  let y := Functor.OverTotal.ofFibre T r₀
  refine ⟨y, ?_, ?_⟩
  · intro i
    have hy : (P.overTotal.map (𝒰.f i).op y).1 = (C i).hom := rfl
    apply total_eq_of_fibre_eq (C i) _ _ hy (hb i)
    calc
      _ = P.map (SubgroupFunctor.coverMap (T := T) 𝒰 i).op
          (Functor.OverTotal.toFibre T y rfl) :=
        Functor.OverTotal.toFibre_naturality
          (SubgroupFunctor.coverMap (T := T) 𝒰 i) y rfl hy
      _ = P.map (SubgroupFunctor.coverMap (T := T) 𝒰 i).op r₀ :=
        congrArg _ (Functor.OverTotal.toFibre_ofFibre T r₀)
      _ = r i := hr₀ i
  · intro y' hy'
    have hbase : y'.1 = T.hom := by
      apply 𝒰.hom_ext
      intro i
      exact (congrArg (fun z => z.1) (hy' i)).trans (ht i).symm
    have hri : ∀ i, P.map (SubgroupFunctor.coverMap (T := T) 𝒰 i).op
        (Functor.OverTotal.toFibre T y' hbase) = r i := by
      intro i
      have hi : (P.overTotal.map (𝒰.f i).op y').1 = (C i).hom := by
        rw [Functor.overTotal_map_fst, hbase]
        rfl
      calc
        _ = Functor.OverTotal.toFibre (C i)
            (P.overTotal.map (𝒰.f i).op y') hi :=
          (Functor.OverTotal.toFibre_naturality
            (SubgroupFunctor.coverMap (T := T) 𝒰 i) y' hbase hi).symm
        _ = r i := Functor.OverTotal.toFibre_congr (C i) (hy' i) hi (hb i)
    apply total_eq_of_fibre_eq T y' y hbase rfl
    rw [Functor.OverTotal.toFibre_ofFibre]
    exact hur₀ _ hri

/-- Relative gluing and gluing of structural maps give unique total gluing. -/
theorem totalAdmissible_isSheafFor_cover (hG : HasEffectiveAdmissibleDescent G)
    (X : Scheme.{u}) (𝒰 : Scheme.OpenCover.{u} X) :
    Presieve.IsSheafFor (totalAdmissiblePresheaf G)
      (Presieve.ofArrows 𝒰.X 𝒰.f) :=
  overTotal_isSheafFor_cover (smallAdmissiblePresheaf G)
    (smallAdmissible_isSheafFor_cover G hG) X 𝒰

private theorem isSheaf_zariski_of_openCover
    (P : Scheme.{u}ᵒᵖ ⥤ Type u)
    (hP : ∀ (X : Scheme.{u}) (𝒰 : Scheme.OpenCover.{u} X),
      Presieve.IsSheafFor P (Presieve.ofArrows 𝒰.X 𝒰.f)) :
    Presieve.IsSheaf Scheme.zariskiTopology P := by
  intro X R hR
  obtain ⟨𝒰, h𝒰⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hR
  apply Presieve.isSheafFor_subsieve_aux P
    ((Sieve.generate_le_iff (Presieve.ofArrows 𝒰.X 𝒰.f) R).mpr h𝒰)
    ((Presieve.isSheafFor_iff_generate _).mp (hP X 𝒰))
  intro Y g _ x t₁ t₂ ht₁ ht₂
  apply (hP Y (𝒰.pullback₁ g)).isSeparatedFor.ext
  rintro _ _ ⟨i⟩
  have hm : (Sieve.generate (Presieve.ofArrows 𝒰.X 𝒰.f)).pullback g
      ((𝒰.pullback₁ g).f i) := by
    exact ⟨_, 𝒰.pullbackHom g i, 𝒰.f i, ⟨i⟩, 𝒰.pullbackHom_map g i⟩
  exact (ht₁ _ hm).trans (ht₂ _ hm).symm

/-- Actual admissible families form a big Zariski sheaf once effective
admissibility of the matching subgroup has been established. -/
theorem totalAdmissible_isSheaf (hG : HasEffectiveAdmissibleDescent G) :
    Presieve.IsSheaf Scheme.zariskiTopology (totalAdmissiblePresheaf G) :=
  isSheaf_zariski_of_openCover (totalAdmissiblePresheaf G)
    (totalAdmissible_isSheafFor_cover G hG)

end Langlands.GroupScheme.TorusSubgroupModuli
