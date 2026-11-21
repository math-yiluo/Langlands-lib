import Langlands.Cohomology.CoinducedFilteredAcyclic

/-! # A local criterion for vanishing group cohomology in a filtered colimit -/

namespace Langlands.Cohomology.CoinducedFilteredAcyclic

open CategoryTheory CategoryTheory.Limits

universe u

variable {k G : Type u} [CommRing k] [Group G] [Finite G]
  {J : Type u} [SmallCategory J] [IsFiltered J] {F : J ⥤ Rep.{u} k G}
  {c : Cocone F}

/-- Every family of degree-`n` cochain coordinates at a stage maps into
a subrepresentation with vanishing degree-`n` group cohomology after
a transition. -/
def EventuallyAcyclicSubrepresentations (F : J ⥤ Rep.{u} k G) (n : ℕ) : Prop :=
  ∀ (i : J) (y : (Fin n → G) → F.obj i),
    ∃ (j : J) (f : i ⟶ j) (A : Rep.{u} k G) (a : A ⟶ F.obj j),
      Function.Injective a ∧ IsZero (groupCohomology A n) ∧
        ∀ t, ∃ z : A, a z = F.map f (y t)

/-- Group cohomology of a filtered colimit vanishes in degree `n` if every
family of degree-`n` coordinates at a stage eventually lands inside a
subrepresentation with vanishing group cohomology in that degree. -/
theorem isZero_groupCohomology_of_eventually_acyclic_subrepresentation
    (hc : IsColimit c) (n : ℕ)
    (hlocal : EventuallyAcyclicSubrepresentations F n) :
    IsZero (groupCohomology c.pt n) := by
  classical
  let Q := groupCohomology.cochainsFunctor k G
  let C := Q.mapCocone c
  let next := (ComplexShape.up ℕ).next n
  let prev := (ComplexShape.up ℕ).prev n
  have comm_apply {A B : CochainComplex (ModuleCat.{u} k) ℕ} (p : A ⟶ B)
      (i j : ℕ) (s : A.X i) : B.d i j (p.f i s) = p.f j (A.d i j s) :=
    ConcreteCategory.congr_hom (p.comm i j) s
  change IsZero (C.pt.homology n)
  rw [← HomologicalComplex.exactAt_iff_isZero_homology, HomologicalComplex.exactAt_iff,
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  change C.pt.X n at x
  change C.pt.d n next x = 0 at hx
  obtain ⟨i, y, hy⟩ := exists_family_rep hc x
  have hiy : (C.ι.app i).f n y = x := funext hy
  have hdy : (C.ι.app i).f next ((Q.obj (F.obj i)).d n next y) = 0 := by
    exact (comm_apply (C.ι.app i) n next y).symm.trans
      ((congrArg (fun s => C.pt.d n next s) hiy).trans hx)
  obtain ⟨j, f, hf⟩ :=
    exists_family_eq_zero hc ((Q.obj (F.obj i)).d n next y) (fun t => congrFun hdy t)
  let y' : (Q.obj (F.obj j)).X n := (Q.map (F.map f)).f n y
  have hcyc : (Q.obj (F.obj j)).d n next y' = 0 :=
    (comm_apply (Q.map (F.map f)) n next y).trans (funext hf)
  obtain ⟨l, g, A, a, ha, hAn, hys⟩ := hlocal j y'
  choose z hz using hys
  have hza : (Q.map a).f n z = (Q.map (F.map g)).f n y' := funext hz
  have hmono : Function.Injective ((Q.map a).f next) :=
    fun p q hpq => funext fun t => ha (congrFun hpq t)
  have hdz : (Q.obj A).d n next z = 0 := by
    apply hmono
    calc
      _ = (Q.obj (F.obj l)).d n next ((Q.map a).f n z) :=
        (comm_apply (Q.map a) n next z).symm
      _ = (Q.obj (F.obj l)).d n next ((Q.map (F.map g)).f n y') :=
        congrArg (fun s => (Q.obj (F.obj l)).d n next s) hza
      _ = (Q.map (F.map g)).f next ((Q.obj (F.obj j)).d n next y') :=
        comm_apply (Q.map (F.map g)) n next y'
      _ = (Q.map a).f next 0 := by rw [hcyc, map_zero, map_zero]
  have hex : (Q.obj A).ExactAt n := (HomologicalComplex.exactAt_iff_isZero_homology _ _).2 hAn
  obtain ⟨w, hw⟩ := (ShortComplex.moduleCat_exact_iff _).1 hex z hdz
  change (Q.obj A).d prev n w = z at hw
  have hwl : (Q.obj (F.obj l)).d prev n ((Q.map a).f prev w) =
      (Q.map (F.map g)).f n y' :=
    (comm_apply (Q.map a) prev n w).trans
      ((congrArg (fun s => (Q.map a).f n s) hw).trans hza)
  have hcocone {i j : J} (p : i ⟶ j) (s : (Q.obj (F.obj i)).X n) :
      (C.ι.app j).f n ((Q.map (F.map p)).f n s) = (C.ι.app i).f n s :=
    ConcreteCategory.congr_hom (congrArg (fun φ => HomologicalComplex.Hom.f φ n) (C.w p)) s
  refine ⟨(C.ι.app l).f prev ((Q.map a).f prev w), ?_⟩
  change C.pt.d prev n ((C.ι.app l).f prev ((Q.map a).f prev w)) = x
  calc
    _ = (C.ι.app l).f n ((Q.obj (F.obj l)).d prev n ((Q.map a).f prev w)) :=
      comm_apply (C.ι.app l) prev n ((Q.map a).f prev w)
    _ = (C.ι.app l).f n ((Q.map (F.map g)).f n y') :=
      congrArg (fun s => (C.ι.app l).f n s) hwl
    _ = (C.ι.app j).f n y' := hcocone g y'
    _ = (C.ι.app i).f n y := hcocone f y
    _ = x := hiy

end Langlands.Cohomology.CoinducedFilteredAcyclic
