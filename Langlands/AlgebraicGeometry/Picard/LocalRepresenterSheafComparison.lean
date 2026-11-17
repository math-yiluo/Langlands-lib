import Langlands.AlgebraicGeometry.Picard.LocalRepresenterRelation
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtalePresentationComparison
import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-! # Recovering the sheaf from an effective local scheme descent -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.LocalRepresenter

variable {S U : Scheme.{u}} (p : U ⟶ S)
    {F : (Over S)ᵒᵖ ⥤ Type v} {M : Over U}
    (e : ((Over.map p).op ⋙ F).RepresentableBy M)

/-- The local relation is cartesian over the original covering base. -/
theorem cartesian :
    IsPullback (first p) (second p e ≫ M.hom) (M.hom ≫ p) p := by
  have h : second p e ≫ M.hom = pullback.snd (M.hom ≫ p) p := (secondOver p e).w
  rw [h]
  exact IsPullback.of_hasPullback _ _

/-- Universal chart map after a temporary universe lift of the presheaf. -/
def liftedChartMap :
    uliftYoneda.{max (u + 1) v}.obj (chart p (M := M)) ⟶
      (F ⋙ uliftFunctor.{u + 1}) :=
  uliftYonedaEquiv.symm ⟨family p e⟩

@[simp]
theorem liftedChartMap_apply {T : Over S} (a : T ⟶ chart p (M := M)) :
    (liftedChartMap p e).app (op T) ⟨a⟩ = ⟨F.map a.op (family p e)⟩ := rfl

/-- A local representing chart is locally surjective on the full big étale site. -/
theorem liftedChartMap_locallySurjective [Etale p] [Surjective p] :
    CategoryTheory.Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
      (liftedChartMap p e) := by
  constructor
  intro T x
  let V : Over U := (Over.pullback p).obj T
  let a : (Over.map p).obj V ⟶ T := (Over.mapPullbackAdj p).counit.app T
  have : Etale a.left := inferInstanceAs (Etale (pullback.fst T.hom p))
  have : Surjective a.left := inferInstanceAs (Surjective (pullback.fst T.hom p))
  let b : V ⟶ M := e.homEquiv.symm (F.map a.op x.down)
  apply (Scheme.etaleTopology.over S).superset_covering ?_
    (AlgebraicSpace.generate_singleton_mem_etaleTopology a)
  rw [Sieve.generate_le_iff, Presieve.singleton_le_iff]
  refine ⟨⟨(Over.map p).map b⟩, ?_⟩
  apply ULift.ext
  change F.map ((Over.map p).map b).op (family p e) = F.map a.op x.down
  exact (e.homEquiv_eq b).symm.trans (e.homEquiv.apply_symm_apply _)

/-- A surjective étale map remains locally surjective in the larger Yoneda
universe used for the comparison. -/
theorem liftedYonedaMap_locallySurjective {W N : Over S} (q : W ⟶ N)
    [Etale q.left] [Surjective q.left] :
    CategoryTheory.Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
      (uliftYoneda.{max (u + 1) v}.map q) := by
  constructor
  intro T x
  apply (Scheme.etaleTopology.over S).superset_covering ?_
    ((Scheme.etaleTopology.over S).pullback_stable x.down
      (AlgebraicSpace.generate_singleton_mem_etaleTopology q))
  intro V g hg
  obtain ⟨Z, t, q', hq', hcomp⟩ := hg
  cases hq'
  refine ⟨⟨t⟩, ?_⟩
  apply ULift.ext
  exact hcomp

/-- An invariant cartesian scheme descent identifies exactly those chart
maps which classify the same family. -/
theorem same_kernel {N : Over S} (q : M.left ⟶ N.left)
    (hq : IsPullback q M.hom N.hom p)
    (hi : first p ≫ q = second p e ≫ q)
    {T : Over S} (a b : T ⟶ chart p (M := M)) :
    F.map a.op (family p e) = F.map b.op (family p e) ↔
      a ≫ Over.homMk q hq.w = b ≫ Over.homMk q hq.w := by
  let qOver : chart p (M := M) ⟶ N := Over.homMk q hq.w
  have hiOver : firstOver p ≫ qOver = secondOverS p e ≫ qOver := by
    apply Over.OverMorphism.ext
    exact hi
  constructor
  · intro h
    change a ≫ qOver = b ≫ qOver
    calc
      a ≫ qOver = kernelLift p e a b h ≫ firstOver p ≫ qOver := by
        rw [← Category.assoc, kernelLift_first]
      _ = kernelLift p e a b h ≫ secondOverS p e ≫ qOver := by rw [hiOver]
      _ = b ≫ qOver := by rw [← Category.assoc, kernelLift_second]
  · intro h
    have hab : a.left ≫ (M.hom ≫ p) = (b.left ≫ M.hom) ≫ p := by
      simpa [chart, Category.assoc] using a.w.trans b.w.symm
    let r : T.left ⟶ overlap p (M := M) :=
      (cartesian p e).lift a.left (b.left ≫ M.hom) hab
    have hr1 : r ≫ first p = a.left := (cartesian p e).lift_fst _ _ _
    have hr2 : (r ≫ second p e) ≫ M.hom = b.left ≫ M.hom := by
      simpa only [Category.assoc] using (cartesian p e).lift_snd a.left
        (b.left ≫ M.hom) hab
    have hrq : (r ≫ second p e) ≫ q = b.left ≫ q := by
      calc
        (r ≫ second p e) ≫ q = (r ≫ first p) ≫ q := by
          simpa only [Category.assoc] using congrArg (fun k => r ≫ k) hi.symm
        _ = a.left ≫ q := by rw [hr1]
        _ = b.left ≫ q := congrArg Over.Hom.left h
    have hr3 : r ≫ second p e = b.left := hq.hom_ext hrq hr2
    let rOver : T ⟶ overlapOverS p (M := M) := Over.homMk r (by
      have hs : second p e ≫ M.hom = pullback.snd (M.hom ≫ p) p :=
        (secondOver p e).w
      change r ≫ (pullback.snd (M.hom ≫ p) p ≫ p) = T.hom
      rw [← hs, ← Category.assoc, ← Category.assoc, hr3]
      exact b.w)
    have hfirst : rOver ≫ firstOver p = a := by
      apply Over.OverMorphism.ext
      exact hr1
    have hsecond : rOver ≫ secondOverS p e = b := by
      apply Over.OverMorphism.ext
      exact hr3
    simpa only [hfirst, hsecond] using kernel_w p e rOver

/-- Lifted representables are sheaves on the full big étale slice site. -/
theorem liftedYoneda_isSheaf (N : Over S) :
    CategoryTheory.Presheaf.IsSheaf (Scheme.etaleTopology.over S)
      (uliftYoneda.{max (u + 1) v}.obj N) := by
  rw [isSheaf_iff_isSheaf_of_type]
  exact Presieve.isSheaf_of_le _
    (Sites.etaleTopologyOver_le_fppfTopologyOver S)
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (J := Scheme.fppfTopology.over S) _)

/-- An invariant cartesian scheme descent of a local representer represents
the original étale sheaf, with no restriction on its value universe. -/
def representableByDescent [Etale p] [Surjective p]
    (hF : Presieve.IsSheaf (Scheme.etaleTopology.over S) F)
    (N : Over S) (q : M.left ⟶ N.left)
    (hq : IsPullback q M.hom N.hom p)
    (hi : first p ≫ q = second p e ≫ q) : F.RepresentableBy N := by
  let qOver : chart p (M := M) ⟶ N := Over.homMk q hq.w
  have : Etale qOver.left :=
    MorphismProperty.of_isPullback (P := @Etale) hq.flip inferInstance
  have : Surjective qOver.left :=
    MorphismProperty.of_isPullback (P := @Surjective) hq.flip inferInstance
  let H : Sheaf (Scheme.etaleTopology.over S) (Type (max (u + 1) v)) :=
    ⟨uliftYoneda.{max (u + 1) v}.obj (chart p (M := M)),
      liftedYoneda_isSheaf.{u, v} (chart p)⟩
  let F' : Sheaf (Scheme.etaleTopology.over S) (Type (max (u + 1) v)) :=
    ⟨F ⋙ uliftFunctor.{u + 1},
      (isSheaf_iff_isSheaf_of_type _ _).mpr
        (Presieve.isSheaf_comp_uliftFunctor _ hF)⟩
  let G : Sheaf (Scheme.etaleTopology.over S) (Type (max (u + 1) v)) :=
    ⟨uliftYoneda.{max (u + 1) v}.obj N, liftedYoneda_isSheaf.{u, v} N⟩
  let a : H ⟶ F' := ObjectProperty.homMk (liftedChartMap p e)
  let b : H ⟶ G := ObjectProperty.homMk (uliftYoneda.{max (u + 1) v}.map qOver)
  have ha : Sheaf.IsLocallySurjective a := liftedChartMap_locallySurjective p e
  have hb : Sheaf.IsLocallySurjective b := liftedYonedaMap_locallySurjective.{u, v} qOver
  have hker : ∀ (T : (Over S)ᵒᵖ) (x y : H.obj.obj T),
      a.hom.app T x = a.hom.app T y ↔ b.hom.app T x = b.hom.app T y := by
    intro T x y
    change ULift.up (F.map x.down.op (family p e)) =
      ULift.up (F.map y.down.op (family p e)) ↔
        ULift.up (x.down ≫ qOver) = ULift.up (y.down ≫ qOver)
    simpa only [ULift.up_inj] using same_kernel p e q hq hi x.down y.down
  let d := (Langlands.CategoryTheory.Sites.exists_iso_of_isLocallySurjective_of_same_kernel
    a b ha hb hker).choose
  let iso : uliftYoneda.{max (u + 1) v}.obj N ≅ F ⋙ uliftFunctor.{u + 1} :=
    ((sheafToPresheaf (Scheme.etaleTopology.over S) (Type (max (u + 1) v))).mapIso d).symm
  exact Functor.representableByUliftFunctorEquiv
    ((Functor.RepresentableBy.equivUliftYonedaIso _ N).symm iso)

end Langlands.AlgebraicGeometry.Picard.LocalRepresenter
