import Langlands.GaloisCohomology.Global.PoitouTate.BaseCase.Kummer
import Langlands.GaloisCohomology.Global.Units.PicardCapitulation
import Langlands.GaloisCohomology.Global.Abelianization.Presentation

/-!
# Classes of `H_c¹(G_S, 𝒪_Sˣ)` from `S`-invariant units and local units

With the notation of `Langlands.GaloisCohomology.Global.PoitouTate.BaseCase.Kummer`, a class of
`H_c¹(G_S, E; (K̄_vˣ)_{v ∈ S})` (`E = 𝒪_{K_S,S}ˣ`) is represented by a pair `(x, (y_v)_v)`: a
`1`-cocycle `x` of `G_S` in `E` and points `y_v ∈ K̄_vˣ` with `x|_{G_{K_v}} = d y_v`. Every such
class comes from a *datum* `(t, (a_v)_{v ∈ S})`: an `S`-invariant unit `t ∈ K_Sˣ` (`σ(t)/t ∈ E` for
all `σ`) and local units `a_v ∈ K_vˣ`, through the cocycle `(σ ↦ σ(t)/t, (ι_v(t) a_v)_v)`
(`unitsData`, surjective by Hilbert 90 for `K_Sˣ`: `unitsData_surjective`). The datum also has a
class in the `S`-idèle class group, `sPresentation ((a_v)_v, -div(t))` (`unitsClass`, surjective by
the principal ideal theorem in the form `divAbove_surjective`), and `unitsData` vanishes on the
data of class zero (`unitsData_eq_zero_of_unitsClass_eq_zero`): such a datum is, up to an
`S`-unit, `(α, α^{-1})` for `α ∈ Kˣ`, whose cocycle is a coboundary.

The general part (`dataCochain`, `dataCycle`, `dataHom`) is stated for an arbitrary family of local
groups and local coefficient maps.
-/

namespace Langlands.GaloisCohomology.PoitouTate.Internal

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
  IsLocalRing

universe u

noncomputable section

section General

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {U : Rep.{u} k G} [IsSmoothRep U] (Ωᵥ : ∀ v, Rep.{u} k (H v)) [∀ v, IsSmoothRep (Ωᵥ v)]
  (a : ∀ v, Rep.res (φ v : H v →* G) U ⟶ Ωᵥ v)

/-- A family of points of the local modules, as a family of constant `0`-cochains. -/
def piConst (y : ∀ v, Ωᵥ v) : (piComplex fun v => cochains (Ωᵥ v)).X 0 :=
  show ∀ v, (cochains (Ωᵥ v)).X 0 from fun v => zeroCochain (Ωᵥ v) (y v)

theorem piConst_apply (y : ∀ v, Ωᵥ v) (v : ι) : piConst Ωᵥ y v = zeroCochain (Ωᵥ v) (y v) :=
  rfl

theorem piConst_add (y y' : ∀ v, Ωᵥ v) : piConst Ωᵥ (y + y') = piConst Ωᵥ y + piConst Ωᵥ y' :=
  rfl

/-- The condition on `(x, y)` to be a `1`-cocycle with compact support: `x|_{H_v} = d y_v`. -/
def DataCond (x : (cochains U).X 1) (y : ∀ v, Ωᵥ v) : Prop :=
  ∀ v (σ : H v), (a v).hom (cochainOf U x ![(φ v : H v →* G) σ]) = (Ωᵥ v).ρ σ (y v) - y v

/-- The cochain with compact support `(x, y)` in degree `1`. -/
def dataCochain (x : (cochains U).X 1) (y : ∀ v, Ωᵥ v) :
    (compactSupportCochains φ U Ωᵥ a).X 1 :=
  compactMkSucc φ U Ωᵥ a (n := 0) x (piConst Ωᵥ y)

theorem dataCochain_add (x x' : (cochains U).X 1) (y y' : ∀ v, Ωᵥ v) :
    dataCochain φ Ωᵥ a (x + x') (y + y') = dataCochain φ Ωᵥ a x y + dataCochain φ Ωᵥ a x' y' :=
  rfl

theorem localRes_one_eq_d_piConst (x : (cochains U).X 1) (y : ∀ v, Ωᵥ v)
    (hy : DataCond φ Ωᵥ a x y) :
    ((localRes φ U Ωᵥ a).f (0 + 1)).hom x =
      ((piComplex fun v => cochains (Ωᵥ v)).d 0 (0 + 1)).hom (piConst Ωᵥ y) := by
  funext v
  rw [piComplex_d_hom_apply, piConst_apply]
  apply cochainOf_injective
  funext h
  rw [cochainOf_d_zeroCochain]
  have hh : (⇑(φ v : H v →* G) ∘ h) = ![(φ v : H v →* G) (h 0)] := by
    funext i
    fin_cases i
    rfl
  change (a v).hom (cochainOf U x (⇑(φ v : H v →* G) ∘ h)) = _
  rw [hh]
  exact hy v (h 0)

theorem d_dataCochain (x : (cochains U).X 1) (y : ∀ v, Ωᵥ v)
    (hx : ((cochains U).d 1 2).hom x = 0) (hy : DataCond φ Ωᵥ a x y) :
    ((compactSupportCochains φ U Ωᵥ a).d 1 2).hom (dataCochain φ Ωᵥ a x y) = 0 := by
  refine (d_compactMkSucc φ U Ωᵥ a (n := 0) x (piConst Ωᵥ y)).trans ?_
  rw [localRes_one_eq_d_piConst φ Ωᵥ a x y hy, sub_self]
  change compactMkSucc φ U Ωᵥ a (((cochains U).d 1 2).hom x) 0 = 0
  rw [hx]
  rfl

/-- The cocycle with compact support `(x, y)`. -/
def dataCycle (x : (cochains U).X 1) (y : ∀ v, Ωᵥ v) (hx : ((cochains U).d 1 2).hom x = 0)
    (hy : DataCond φ Ωᵥ a x y) : (compactSupportCochains φ U Ωᵥ a).cycles 1 :=
  (compactSupportCochains φ U Ωᵥ a).cyclesMk (dataCochain φ Ωᵥ a x y) 2 (by simp)
    (d_dataCochain φ Ωᵥ a x y hx hy)

theorem iCycles_dataCycle (x : (cochains U).X 1) (y : ∀ v, Ωᵥ v)
    (hx : ((cochains U).d 1 2).hom x = 0) (hy : DataCond φ Ωᵥ a x y) :
    ((compactSupportCochains φ U Ωᵥ a).iCycles 1).hom (dataCycle φ Ωᵥ a x y hx hy) =
      dataCochain φ Ωᵥ a x y :=
  (compactSupportCochains φ U Ωᵥ a).i_cyclesMk _ _ _ _

theorem dataCycle_congr {x x' : (cochains U).X 1} {y y' : ∀ v, Ωᵥ v} (ex : x = x') (ey : y = y')
    (hx : ((cochains U).d 1 2).hom x = 0) (hx' : ((cochains U).d 1 2).hom x' = 0)
    (hy : DataCond φ Ωᵥ a x y) (hy' : DataCond φ Ωᵥ a x' y') :
    dataCycle φ Ωᵥ a x y hx hy = dataCycle φ Ωᵥ a x' y' hx' hy' := by
  subst ex ey
  rfl

omit [∀ v, IsTopologicalGroup (H v)] [∀ v, IsSmoothRep (Ωᵥ v)] in
theorem dataCond_add {x x' : (cochains U).X 1} {y y' : ∀ v, Ωᵥ v} (hy : DataCond φ Ωᵥ a x y)
    (hy' : DataCond φ Ωᵥ a x' y') : DataCond φ Ωᵥ a (x + x') (y + y') := fun v σ => by
  rw [cochainOf_add, Pi.add_apply, map_add, hy v σ, hy' v σ, Pi.add_apply, map_add]
  abel

omit [∀ v, IsTopologicalGroup (H v)] [∀ v, IsSmoothRep (Ωᵥ v)] in
theorem dataCond_zero : DataCond φ Ωᵥ a (0 : (cochains U).X 1) (0 : ∀ v, Ωᵥ v) := fun v σ => by
  rw [cochainOf_zero, Pi.zero_apply, map_zero, Pi.zero_apply, map_zero, sub_zero]

/-- A homomorphism from a group of data to `H_c¹`. -/
def dataHom {D : Type u} [AddCommGroup D] (xOf : D →+ (cochains U).X 1) (yOf : D →+ (∀ v, Ωᵥ v))
    (hx : ∀ d, ((cochains U).d 1 2).hom (xOf d) = 0) (hy : ∀ d, DataCond φ Ωᵥ a (xOf d) (yOf d)) :
    D →+ compactSupportCohomology φ U Ωᵥ a 1 where
  toFun d := ((compactSupportCochains φ U Ωᵥ a).homologyπ 1).hom
    (dataCycle φ Ωᵥ a (xOf d) (yOf d) (hx d) (hy d))
  map_zero' := by
    rw [dataCycle_congr φ Ωᵥ a (map_zero xOf) (map_zero yOf) (hx 0) (map_zero _) (hy 0)
      (dataCond_zero φ Ωᵥ a)]
    have h0 : dataCycle φ Ωᵥ a (0 : (cochains U).X 1) (0 : ∀ v, Ωᵥ v) (map_zero _)
        (dataCond_zero φ Ωᵥ a) = 0 := by
      apply (ModuleCat.mono_iff_injective ((compactSupportCochains φ U Ωᵥ a).iCycles 1)).1
        inferInstance
      rw [map_zero, iCycles_dataCycle]
      rfl
    rw [h0]
    exact map_zero _
  map_add' d d' := by
    refine Eq.trans ?_ (map_add ((compactSupportCochains φ U Ωᵥ a).homologyπ 1).hom _ _)
    congr 1
    apply (ModuleCat.mono_iff_injective ((compactSupportCochains φ U Ωᵥ a).iCycles 1)).1
      inferInstance
    rw [map_add ((compactSupportCochains φ U Ωᵥ a).iCycles 1).hom, iCycles_dataCycle,
      iCycles_dataCycle, iCycles_dataCycle, map_add xOf, map_add yOf]
    rfl

theorem dataHom_apply {D : Type u} [AddCommGroup D] (xOf : D →+ (cochains U).X 1)
    (yOf : D →+ (∀ v, Ωᵥ v)) (hx : ∀ d, ((cochains U).d 1 2).hom (xOf d) = 0)
    (hy : ∀ d, DataCond φ Ωᵥ a (xOf d) (yOf d)) (d : D) :
    dataHom φ Ωᵥ a xOf yOf hx hy d = ((compactSupportCochains φ U Ωᵥ a).homologyπ 1).hom
      (dataCycle φ Ωᵥ a (xOf d) (yOf d) (hx d) (hy d)) :=
  rfl

/-- Every `1`-cocycle with compact support is a `dataCycle`. -/
theorem exists_dataCycle_eq (c : (compactSupportCochains φ U Ωᵥ a).cycles 1) :
    ∃ (x : (cochains U).X 1) (y : ∀ v, Ωᵥ v) (hx : ((cochains U).d 1 2).hom x = 0)
      (hy : DataCond φ Ωᵥ a x y), c = dataCycle φ Ωᵥ a x y hx hy := by
  let q : (cochains U).X 1 × (piComplex fun v => cochains (Ωᵥ v)).X 0 :=
    ((compactSupportCochains φ U Ωᵥ a).iCycles 1).hom c
  have hd : ((compactSupportCochains φ U Ωᵥ a).d (0 + 1) (0 + 1 + 1)).hom
      (compactMkSucc φ U Ωᵥ a (n := 0) q.1 q.2) = compactMkSucc φ U Ωᵥ a (n := 1) 0 0 :=
    hom_apply_hom_apply_of_comp_eq ((compactSupportCochains φ U Ωᵥ a).iCycles_d 1 2) c
  have hd' := (compactMkSucc_eq_iff φ U Ωᵥ a _ _ _ _).1
    ((d_compactMkSucc φ U Ωᵥ a (n := 0) q.1 q.2).symm.trans hd)
  have hd2 : ((localRes φ U Ωᵥ a).f (0 + 1)).hom q.1 -
      ((piComplex fun v => cochains (Ωᵥ v)).d 0 (0 + 1)).hom q.2 = 0 := hd'.2
  let y : ∀ v, Ωᵥ v := fun v => cochainOf (Ωᵥ v) (q.2 v) Fin.elim0
  have hyy : q.2 = piConst Ωᵥ y := funext fun v => cochainOf_injective (funext fun σ => by
    rw [Subsingleton.elim σ Fin.elim0]
    rfl)
  have hy : DataCond φ Ωᵥ a q.1 y := fun v σ => by
    have e := congrArg (fun w => cochainOf (Ωᵥ v) (w v) ![σ]) (sub_eq_zero.1 hd2)
    rw [hyy] at e
    have e' : cochainOf (Ωᵥ v) (((localRes φ U Ωᵥ a).f (0 + 1)).hom q.1 v) ![σ] =
        cochainOf (Ωᵥ v) (((cochains (Ωᵥ v)).d 0 1).hom (zeroCochain (Ωᵥ v) (y v))) ![σ] := e
    rw [cochainOf_d_zeroCochain] at e'
    refine Eq.trans ?_ e'
    have hh : (⇑(φ v : H v →* G) ∘ ![σ]) = ![(φ v : H v →* G) σ] := by
      funext i
      fin_cases i
      rfl
    change _ = (a v).hom (cochainOf U q.1 (⇑(φ v : H v →* G) ∘ ![σ]))
    rw [hh]
  refine ⟨q.1, y, hd'.1, hy, ?_⟩
  apply (ModuleCat.mono_iff_injective ((compactSupportCochains φ U Ωᵥ a).iCycles 1)).1 inferInstance
  rw [iCycles_dataCycle]
  exact Prod.ext rfl hyy

/-- `dataHom` is surjective when every pair `(x, y)` with the cocycle condition comes from a
datum. -/
theorem dataHom_surjective {D : Type u} [AddCommGroup D] (xOf : D →+ (cochains U).X 1)
    (yOf : D →+ (∀ v, Ωᵥ v)) (hx : ∀ d, ((cochains U).d 1 2).hom (xOf d) = 0)
    (hy : ∀ d, DataCond φ Ωᵥ a (xOf d) (yOf d))
    (hd : ∀ (x : (cochains U).X 1) (y : ∀ v, Ωᵥ v), ((cochains U).d 1 2).hom x = 0 →
      DataCond φ Ωᵥ a x y → ∃ d, xOf d = x ∧ yOf d = y) :
    Function.Surjective (dataHom φ Ωᵥ a xOf yOf hx hy) := by
  intro h
  obtain ⟨c, rfl⟩ := homologyπ_surjective _ 1 h
  obtain ⟨x, y, hx', hy', rfl⟩ := exists_dataCycle_eq φ Ωᵥ a c
  obtain ⟨d, hxd, hyd⟩ := hd x y hx' hy'
  exact ⟨d, (dataHom_apply φ Ωᵥ a xOf yOf hx hy d).trans
    (congrArg _ (dataCycle_congr φ Ωᵥ a hxd hyd _ _ _ _))⟩

/-- The class of `(d α, (a_v α)_v)` is zero. -/
theorem homologyπ_dataCycle_of_boundary (α : U) (x : (cochains U).X 1) (y : ∀ v, Ωᵥ v)
    (hx : ((cochains U).d 1 2).hom x = 0) (hy : DataCond φ Ωᵥ a x y)
    (hxα : ∀ σ : G, cochainOf U x ![σ] = U.ρ σ α - α) (hyα : ∀ v, y v = (a v).hom α) :
    ((compactSupportCochains φ U Ωᵥ a).homologyπ 1).hom (dataCycle φ Ωᵥ a x y hx hy) = 0 := by
  refine (homologyπ_succ_eq_zero_iff _ 0 (dataCycle φ Ωᵥ a x y hx hy)).2
    ⟨compactMkZero φ U Ωᵥ a (zeroCochain U α), ?_⟩
  refine (d_compactMkZero φ U Ωᵥ a (zeroCochain U α)).trans ?_
  rw [iCycles_dataCycle]
  refine (compactMkSucc_eq_iff φ U Ωᵥ a _ _ _ _).2 ⟨?_, ?_⟩
  · apply cochainOf_injective
    funext σ
    rw [cochainOf_d_zeroCochain]
    have hσ : σ = ![σ 0] := by
      funext i
      fin_cases i
      rfl
    rw [hσ, hxα]
    rfl
  · funext v
    rw [piConst_apply]
    apply cochainOf_injective
    funext h
    change (a v).hom (cochainOf U (zeroCochain U α) (⇑(φ v : H v →* G) ∘ h)) = _
    rw [cochainOf_zeroCochain, cochainOf_zeroCochain, hyα]

theorem dataHom_eq_zero_of_boundary {D : Type u} [AddCommGroup D] (xOf : D →+ (cochains U).X 1)
    (yOf : D →+ (∀ v, Ωᵥ v)) (hx : ∀ d, ((cochains U).d 1 2).hom (xOf d) = 0)
    (hy : ∀ d, DataCond φ Ωᵥ a (xOf d) (yOf d)) (d : D) (α : U)
    (hxα : ∀ σ : G, cochainOf U (xOf d) ![σ] = U.ρ σ α - α) (hyα : ∀ v, yOf d v = (a v).hom α) :
    dataHom φ Ωᵥ a xOf yOf hx hy d = 0 :=
  (dataHom_apply φ Ωᵥ a xOf yOf hx hy d).trans
    (homologyπ_dataCycle_of_boundary φ Ωᵥ a α _ _ _ _ hxα hyα)

/-- A `1`-cocycle of `U` whose image in `X` has `H¹(X) = 0` is the coboundary of a point of `X`. -/
theorem exists_coboundary_of_subsingleton {X : Rep.{u} k G} [IsSmoothRep X] (j : U ⟶ X)
    (hX : Subsingleton (cohomology X 1)) (x : (cochains U).X 1)
    (hx : ((cochains U).d 1 2).hom x = 0) :
    ∃ T : X, ∀ σ : G, j.hom (cochainOf U x ![σ]) = X.ρ σ T - T := by
  have hx' : ((cochains X).d 1 (1 + 1)).hom ((coeffCochainsMap j).f 1 x) = 0 :=
    (hom_apply_hom_apply_eq_of_comp_eq ((coeffCochainsMap j).comm 1 2) x).trans
      (by rw [hx, map_zero])
  obtain ⟨z, hz⟩ := exists_iCycles_eq_of_d_eq_zero _ 1 _ hx'
  have h0 : ((cochains X).homologyπ (0 + 1)).hom z = 0 :=
    Subsingleton.elim (α := cohomology X 1) _ _
  obtain ⟨w, hw⟩ := (homologyπ_succ_eq_zero_iff _ 0 z).1 h0
  refine ⟨cochainOf X w Fin.elim0, fun σ => ?_⟩
  have e : cochainOf X (((cochains X).d 0 (0 + 1)).hom w) ![σ] =
      cochainOf X ((coeffCochainsMap j).f 1 x) ![σ] :=
    congrArg (fun c => cochainOf X c ![σ]) (hw.trans hz)
  rw [cochainOf_cochainsMap_f] at e
  refine e.symm.trans ?_
  have hw0 : w = zeroCochain X (cochainOf X w Fin.elim0) :=
    cochainOf_injective (funext fun τ => by rw [Subsingleton.elim τ Fin.elim0]; rfl)
  rw [hw0, cochainOf_d_zeroCochain]
  rfl

/-- A datum with zero global part and invariant local points is the image of the local classes of
degree `0`. -/
theorem homologyπ_dataCycle_zero_of_invariant (y : ∀ v, Ωᵥ v)
    (hy0 : ∀ v (σ : H v), (Ωᵥ v).ρ σ (y v) = y v) (hx : ((cochains U).d 1 2).hom 0 = 0)
    (hy : DataCond φ Ωᵥ a 0 y) :
    ((compactSupportCochains φ U Ωᵥ a).homologyπ 1).hom (dataCycle φ Ωᵥ a 0 y hx hy) =
      (GaloisCohomology.localToCompact φ U Ωᵥ a 0).hom
        (fun v => (zeroIso (Ωᵥ v)).inv.hom ⟨y v, (Representation.mem_invariants _ _).2 (hy0 v)⟩) := by
  have hd : ((piComplex fun v => cochains (Ωᵥ v)).d 0 1).hom (piConst Ωᵥ y) = 0 := by
    funext v
    rw [piComplex_d_hom_apply, piConst_apply]
    apply cochainOf_injective
    funext h
    rw [cochainOf_d_zeroCochain, hy0, sub_self]
    rfl
  obtain ⟨c, hc⟩ := exists_iCycles_eq_of_d_eq_zero _ 0 (piConst Ωᵥ y) hd
  have hv : ∀ v, (HomologicalComplex.homologyMap (piProj (fun v => cochains (Ωᵥ v)) v) 0).hom
      (((piComplex fun v => cochains (Ωᵥ v)).homologyπ 0).hom c) =
      (zeroIso (Ωᵥ v)).inv.hom ⟨y v, (Representation.mem_invariants _ _).2 (hy0 v)⟩ := fun v => by
    obtain ⟨z0, hz0, hz0c⟩ := exists_cocycle_zeroIso_inv (Ωᵥ v)
      ⟨y v, (Representation.mem_invariants _ _).2 (hy0 v)⟩
    rw [← ModuleCat.comp_apply, HomologicalComplex.homologyπ_naturality, ModuleCat.comp_apply, ← hz0]
    congr 1
    apply (ModuleCat.mono_iff_injective ((cochains (Ωᵥ v)).iCycles 0)).1 inferInstance
    refine (hom_apply_hom_apply_eq_of_comp_eq (HomologicalComplex.cyclesMap_i _ _) c).trans ?_
    rw [hc, piProj_f_hom_apply, piConst_apply]
    apply cochainOf_injective
    exact (funext fun _ => rfl : cochainOf (Ωᵥ v) (zeroCochain (Ωᵥ v) (y v)) = fun _ => y v).trans
      hz0c.symm
  have h1 : (localCohomologyIso Ωᵥ 0).hom.hom (((piComplex fun v => cochains (Ωᵥ v)).homologyπ 0).hom c) =
      fun v => (zeroIso (Ωᵥ v)).inv.hom ⟨y v, (Representation.mem_invariants _ _).2 (hy0 v)⟩ :=
    funext fun v => (piHomologyIso_hom_apply _ 0 _ v).trans (hv v)
  obtain ⟨c', hc', hc'i⟩ := mappingCoconeNat.exists_homologyδ_homologyπ (localRes φ U Ωᵥ a) 0 c
  have h2 : dataCycle φ Ωᵥ a 0 y hx hy = c' := by
    apply (ModuleCat.mono_iff_injective ((compactSupportCochains φ U Ωᵥ a).iCycles 1)).1
      inferInstance
    rw [iCycles_dataCycle]
    refine Eq.trans ?_ hc'i.symm
    rw [hc]
    rfl
  rw [h2]
  refine hc'.symm.trans ?_
  rw [← h1]
  exact congrArg (mappingCoconeNat.homologyδ _ 0).hom
    (Iso.hom_inv_id_apply (localCohomologyIso Ωᵥ 0) _).symm

theorem dataHom_eq_localToCompact {D : Type u} [AddCommGroup D] (xOf : D →+ (cochains U).X 1)
    (yOf : D →+ (∀ v, Ωᵥ v)) (hx : ∀ d, ((cochains U).d 1 2).hom (xOf d) = 0)
    (hy : ∀ d, DataCond φ Ωᵥ a (xOf d) (yOf d)) (d : D) (hx0 : xOf d = 0) (y : ∀ v, Ωᵥ v)
    (hyd : yOf d = y) (hy0 : ∀ v (σ : H v), (Ωᵥ v).ρ σ (y v) = y v) :
    dataHom φ Ωᵥ a xOf yOf hx hy d =
      (GaloisCohomology.localToCompact φ U Ωᵥ a 0).hom
        (fun v => (zeroIso (Ωᵥ v)).inv.hom ⟨y v, (Representation.mem_invariants _ _).2 (hy0 v)⟩) := by
  have hy' : DataCond φ Ωᵥ a 0 y := fun v σ => by
    rw [cochainOf_zero, Pi.zero_apply, map_zero, hy0, sub_self]
  rw [dataHom_apply, dataCycle_congr φ Ωᵥ a hx0 hyd (hx d) (map_zero _) (hy d) hy']
  exact homologyπ_dataCycle_zero_of_invariant φ Ωᵥ a y hy0 _ hy'

end General

section Concrete

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] (S : Set (HeightOneSpectrum (𝓞 K)))

/-- `σ(t)/t ∈ 𝒪_Sˣ` for an `S`-invariant unit `t`. -/
def sInvRatio (t : sInvariantSubgroup Ω S) (σ : GaloisGroupUnramifiedOutside K Ω S) :
    Additive (maximalSUnits K Ω S) :=
  Additive.ofMul ⟨galUnitsHom K _ σ (t : (maximalUnramifiedOutside K Ω S)ˣ) *
    (t : (maximalUnramifiedOutside K Ω S)ˣ)⁻¹, (mem_sInvariantSubgroup S).1 t.2 σ⟩

omit [IsSepClosure K Ω] in
/-- The image of `σ(t)/t` in `K_Sˣ` is `σ · t - t` (additively). -/
theorem sUnitsToUnits_sInvRatio (t : sInvariantSubgroup Ω S)
    (σ : GaloisGroupUnramifiedOutside K Ω S) :
    (sUnitsToUnits S (maximalUnramifiedOutside K Ω S)).hom (sInvRatio Ω S t σ) =
      (unitsModule K (maximalUnramifiedOutside K Ω S)).ρ σ
          (Additive.ofMul (t : (maximalUnramifiedOutside K Ω S)ˣ)) -
        (show unitsModule K (maximalUnramifiedOutside K Ω S) from
          Additive.ofMul (t : (maximalUnramifiedOutside K Ω S)ˣ)) :=
  rfl

omit [IsSepClosure K Ω] in
theorem sInvRatio_mul (t t' : sInvariantSubgroup Ω S) (σ : GaloisGroupUnramifiedOutside K Ω S) :
    sInvRatio Ω S (t * t') σ = sInvRatio Ω S t σ + sInvRatio Ω S t' σ :=
  Additive.toMul.injective (Subtype.ext (galUnitsHom_mul_inv_eq S σ
    (t : (maximalUnramifiedOutside K Ω S)ˣ) t'))

theorem isLocallyConstant_sInvRatio (t : sInvariantSubgroup Ω S) :
    IsLocallyConstant (sInvRatio Ω S t) := by
  refine IsLocallyConstant.desc _ (sUnitsToUnits S (maximalUnramifiedOutside K Ω S)).hom ?_
    (sUnitsToUnits_injective S _)
  have : (sUnitsToUnits S (maximalUnramifiedOutside K Ω S)).hom ∘ sInvRatio Ω S t =
      fun σ => (unitsModule K (maximalUnramifiedOutside K Ω S)).ρ σ
          (Additive.ofMul (t : (maximalUnramifiedOutside K Ω S)ˣ)) -
        (show unitsModule K (maximalUnramifiedOutside K Ω S) from
          Additive.ofMul (t : (maximalUnramifiedOutside K Ω S)ˣ)) :=
    funext fun σ => sUnitsToUnits_sInvRatio Ω S t σ
  rw [this]
  exact (isLocallyConstant_apply _ _).sub (IsLocallyConstant.const _)

/-- The `1`-cocycle `σ ↦ σ(t)/t` of `G_S` in `𝒪_Sˣ`. -/
def sInvCochain (t : sInvariantSubgroup Ω S) : (cochains (maximalSUnitsModule K Ω S)).X 1 :=
  mkCochain _ (fun σ : Fin 1 → GaloisGroupUnramifiedOutside K Ω S => sInvRatio Ω S t (σ 0))
    ((isLocallyConstant_sInvRatio Ω S t).comp_continuous (continuous_apply 0))

theorem cochainOf_sInvCochain (t : sInvariantSubgroup Ω S)
    (σ : Fin 1 → GaloisGroupUnramifiedOutside K Ω S) :
    cochainOf _ (sInvCochain Ω S t) σ = sInvRatio Ω S t (σ 0) :=
  rfl

theorem sInvCochain_mul (t t' : sInvariantSubgroup Ω S) :
    sInvCochain Ω S (t * t') = sInvCochain Ω S t + sInvCochain Ω S t' :=
  cochainOf_injective (funext fun σ => sInvRatio_mul Ω S t t' (σ 0))

theorem sInvCochain_one : sInvCochain Ω S (1 : sInvariantSubgroup Ω S) = 0 :=
  cochainOf_injective (funext fun σ => Additive.toMul.injective (Subtype.ext (by
    change galUnitsHom K _ (σ 0) 1 * (1 : (maximalUnramifiedOutside K Ω S)ˣ)⁻¹ = 1
    rw [map_one, inv_one, mul_one])))

/-- In `K_Sˣ`, the cocycle `σ ↦ σ(t)/t` is the coboundary of `t`. -/
theorem cochainsMap_sUnitsToUnits_sInvCochain (t : sInvariantSubgroup Ω S) :
    (coeffCochainsMap (sUnitsToUnits S (maximalUnramifiedOutside K Ω S))).f 1 (sInvCochain Ω S t) =
      ((cochains (unitsModule K (maximalUnramifiedOutside K Ω S))).d 0 1).hom
        (zeroCochain _ (Additive.ofMul (t : (maximalUnramifiedOutside K Ω S)ˣ))) := by
  apply cochainOf_injective
  funext σ
  rw [cochainOf_cochainsMap_f]
  exact (sUnitsToUnits_sInvRatio Ω S t (σ 0)).trans (cochainOf_d_zeroCochain _ _ σ).symm

theorem d_sInvCochain (t : sInvariantSubgroup Ω S) :
    ((cochains (maximalSUnitsModule K Ω S)).d 1 2).hom (sInvCochain Ω S t) = 0 := by
  have hinj : Function.Injective
      ((coeffCochainsMap (sUnitsToUnits S (maximalUnramifiedOutside K Ω S))).f 2).hom :=
    fun x y hxy => by
      apply cochainOf_injective
      funext σ
      apply sUnitsToUnits_injective S (maximalUnramifiedOutside K Ω S)
      have := congrFun (congrArg (cochainOf _) hxy) σ
      rwa [cochainOf_cochainsMap_f, cochainOf_cochainsMap_f] at this
  apply hinj
  rw [map_zero]
  have hc := hom_apply_hom_apply_eq_of_comp_eq
    ((coeffCochainsMap (sUnitsToUnits S (maximalUnramifiedOutside K Ω S))).comm 1 2)
    (sInvCochain Ω S t)
  refine hc.symm.trans ?_
  change ((cochains _).d 1 2).hom
    ((coeffCochainsMap (sUnitsToUnits S (maximalUnramifiedOutside K Ω S))).f 1 (sInvCochain Ω S t)) = 0
  rw [cochainsMap_sUnitsToUnits_sInvCochain]
  exact hom_apply_hom_apply_of_comp_eq ((cochains _).d_comp_d 0 1 2) _

variable {Ω}

/-- The units of `K_v` in `K̄_vˣ`. -/
def localUnitsHom (v : HeightOneSpectrum (𝓞 K)) :
    Additive (v.adicCompletion K)ˣ →+
      unitsModule (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) :=
  (MonoidHom.toAdditive (Units.map (algebraMap (v.adicCompletion K)
    (AlgebraicClosure (v.adicCompletion K))).toMonoidHom) :
      Additive (v.adicCompletion K)ˣ →+ Additive (AlgebraicClosure (v.adicCompletion K))ˣ)

/-- An `S`-invariant unit of `K_S` in `K̄_vˣ` (by `ι`). -/
def sInvLocalHom (ι : PlaceEmbeddings K Ω) (v : HeightOneSpectrum (𝓞 K)) :
    Additive (sInvariantSubgroup Ω S) →+
      unitsModule (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) :=
  (maximalUnitsLocalHom ι S v).hom.toAddMonoidHom.comp
    (MonoidHom.toAdditive (sInvariantSubgroup Ω S).subtype :
      Additive (sInvariantSubgroup Ω S) →+ Additive (maximalUnramifiedOutside K Ω S)ˣ)

theorem localUnitsHom_invariant (v : HeightOneSpectrum (𝓞 K))
    (σ : Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K))
    (a : Additive (v.adicCompletion K)ˣ) :
    (unitsModule (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))).ρ σ
      (localUnitsHom v a) = localUnitsHom v a :=
  Additive.toMul.injective (Units.ext (σ.commutes _))

variable (Ω) in
/-- The data of degree `1` with compact support: an `S`-invariant unit `t` of `K_S` and local units
`a_v ∈ K_vˣ` at the places of `S`. -/
abbrev UnitsDatum :=
  Additive (sInvariantSubgroup Ω S) × (∀ v : S, Additive (v.1.adicCompletion K)ˣ)

/-- The local component `a_v + ι_v(t)` (additive notation) of the datum `(t, a)`. -/
def dataLocalHom (ι : PlaceEmbeddings K Ω) :
    UnitsDatum Ω S →+
      (∀ v : S, unitsModule (v.1.adicCompletion K) (AlgebraicClosure (v.1.adicCompletion K))) :=
  AddMonoidHom.pi fun v => (localUnitsHom v.1).comp ((Pi.evalAddMonoidHom _ v).comp
    (AddMonoidHom.snd _ _)) + (sInvLocalHom S ι v.1).comp (AddMonoidHom.fst _ _)

theorem dataLocalHom_apply (ι : PlaceEmbeddings K Ω) (d : UnitsDatum Ω S) (v : S) :
    dataLocalHom S ι d v = localUnitsHom v.1 (d.2 v) + sInvLocalHom S ι v.1 d.1 :=
  rfl

variable (Ω) in
/-- The global component `σ ↦ σ(t)/t` of the datum `(t, a)`. -/
def sInvCochainHom : UnitsDatum Ω S →+ (cochains (maximalSUnitsModule K Ω S)).X 1 where
  toFun d := sInvCochain Ω S (Additive.toMul d.1)
  map_zero' := sInvCochain_one Ω S
  map_add' _ _ := sInvCochain_mul Ω S _ _

theorem sUnitsLocalHom_sInvRatio (ι : PlaceEmbeddings K Ω) (v : S) (t : sInvariantSubgroup Ω S)
    (σ : Gal(AlgebraicClosure (v.1.adicCompletion K)/v.1.adicCompletion K)) :
    (sUnitsLocalHom ι S v.1).hom (sInvRatio Ω S t
      ((localFamily ι S v : _ →* GaloisGroupUnramifiedOutside K Ω S) σ)) =
      (unitsModule (v.1.adicCompletion K) (AlgebraicClosure (v.1.adicCompletion K))).ρ σ
        (sInvLocalHom S ι v.1 (Additive.ofMul t)) - sInvLocalHom S ι v.1 (Additive.ofMul t) := by
  apply Additive.toMul.injective
  apply Units.ext
  change ((ι.finite v.1).comp (maximalUnramifiedOutside K Ω S).val)
      (localizationHom ι S v.1 σ ((t : (maximalUnramifiedOutside K Ω S)ˣ) :
        maximalUnramifiedOutside K Ω S) *
      (((t : (maximalUnramifiedOutside K Ω S)ˣ)⁻¹ : (maximalUnramifiedOutside K Ω S)ˣ) :
        maximalUnramifiedOutside K Ω S)) = _
  rw [map_mul]
  exact congrArg (· * _) (localizationHom_apply ι S v.1 σ _)

theorem dataCond_unitsDatum (ι : PlaceEmbeddings K Ω) (d : UnitsDatum Ω S) :
    DataCond (localFamily ι S)
      (fun v : S => unitsModule (v.1.adicCompletion K) (AlgebraicClosure (v.1.adicCompletion K)))
      (fun v => sUnitsLocalHom ι S v.1) (sInvCochainHom Ω S d) (dataLocalHom S ι d) := fun v σ => by
  rw [dataLocalHom_apply, map_add, localUnitsHom_invariant, add_sub_add_left_eq_sub]
  exact sUnitsLocalHom_sInvRatio S ι v (Additive.toMul d.1) σ

/-- **The classes of the data.** -/
def unitsData (ι : PlaceEmbeddings K Ω) : UnitsDatum Ω S →+ unitsCompact ι S 1 :=
  dataHom (localFamily ι S)
    (fun v : S => unitsModule (v.1.adicCompletion K) (AlgebraicClosure (v.1.adicCompletion K)))
    (fun v => sUnitsLocalHom ι S v.1) (sInvCochainHom Ω S) (dataLocalHom S ι)
    (fun _ => d_sInvCochain Ω S _) (dataCond_unitsDatum S ι)

/-- On data `(1, a)`, `unitsData` is `localToCompact` of the local units. -/
theorem unitsData_zero_left (ι : PlaceEmbeddings K Ω) (a : ∀ v : S, Additive (v.1.adicCompletion K)ˣ) :
    unitsData S ι (0, a) =
      (GaloisCohomology.localToCompact (localFamily ι S) (maximalSUnitsModule K Ω S)
        (fun v : S => unitsModule (v.1.adicCompletion K) (AlgebraicClosure (v.1.adicCompletion K)))
        (fun v => sUnitsLocalHom ι S v.1) 0).hom
        (fun v => (zeroIso _).inv.hom (unitsToInvariants _ _ (a v))) :=
  dataHom_eq_localToCompact (localFamily ι S)
    (fun v : S => unitsModule (v.1.adicCompletion K) (AlgebraicClosure (v.1.adicCompletion K)))
    (fun v => sUnitsLocalHom ι S v.1) (sInvCochainHom Ω S) (dataLocalHom S ι)
    (fun _ => d_sInvCochain Ω S _) (dataCond_unitsDatum S ι) ((0 : Additive (sInvariantSubgroup Ω S)), a)
    (sInvCochain_one Ω S) (fun v => localUnitsHom v.1 (a v))
    (funext fun v => (congrArg (localUnitsHom v.1 (a v) + ·) (map_zero (sInvLocalHom S ι v.1))).trans
      (add_zero _))
    (fun v σ => localUnitsHom_invariant v.1 σ (a v))

variable (Ω) in
/-- An `S`-invariant unit from a coboundary in `K_Sˣ` of a cocycle with values in `𝒪_Sˣ`. -/
theorem toMul_mem_sInvariantSubgroup (T : Additive (maximalUnramifiedOutside K Ω S)ˣ)
    (x : (cochains (maximalSUnitsModule K Ω S)).X 1)
    (hT : ∀ σ, (sUnitsToUnits S (maximalUnramifiedOutside K Ω S)).hom (cochainOf _ x ![σ]) =
      (unitsModule K (maximalUnramifiedOutside K Ω S)).ρ σ T -
        (show unitsModule K (maximalUnramifiedOutside K Ω S) from T)) :
    Additive.toMul T ∈ sInvariantSubgroup Ω S := fun σ => by
  have h' : galUnitsHom K _ σ (Additive.toMul T) * (Additive.toMul T)⁻¹ =
      ((Additive.toMul (cochainOf _ x ![σ]) : maximalSUnits K Ω S) :
        (maximalUnramifiedOutside K Ω S)ˣ) := (congrArg Additive.toMul (hT σ)).symm
  rw [h']
  exact (Additive.toMul (cochainOf _ x ![σ])).2

variable (Ω) in
theorem sInvCochain_eq_of (t : sInvariantSubgroup Ω S) (x : (cochains (maximalSUnitsModule K Ω S)).X 1)
    (hT : ∀ σ, (sUnitsToUnits S (maximalUnramifiedOutside K Ω S)).hom (cochainOf _ x ![σ]) =
      (unitsModule K (maximalUnramifiedOutside K Ω S)).ρ σ
          (Additive.ofMul (t : (maximalUnramifiedOutside K Ω S)ˣ)) -
        (show unitsModule K (maximalUnramifiedOutside K Ω S) from
          Additive.ofMul (t : (maximalUnramifiedOutside K Ω S)ˣ))) :
    sInvCochain Ω S t = x := cochainOf_injective (funext fun σ => by
  have hσ : σ = ![σ 0] := by
    funext i
    fin_cases i
    rfl
  rw [hσ]
  exact sUnitsToUnits_injective S (maximalUnramifiedOutside K Ω S)
    ((sUnitsToUnits_sInvRatio Ω S t (σ 0)).trans (hT (σ 0)).symm))

instance isGalois_algebraicClosure_adicCompletion (v : HeightOneSpectrum (𝓞 K)) :
    IsGalois (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) :=
  IsGalois.mk

/-- An invariant point of `K̄_vˣ` comes from `K_vˣ`. -/
theorem exists_localUnitsHom_eq (v : HeightOneSpectrum (𝓞 K))
    (y : unitsModule (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)))
    (hy : ∀ σ, (unitsModule (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))).ρ σ y = y) :
    ∃ a, localUnitsHom v a = y := by
  obtain ⟨a, ha⟩ := unitsToInvariants_surjective (v.adicCompletion K)
    (AlgebraicClosure (v.adicCompletion K)) ⟨y, (Representation.mem_invariants _ _).2 hy⟩
  exact ⟨a, congrArg Subtype.val ha⟩

theorem exists_unitsDatum (ι : PlaceEmbeddings K Ω) (x : (cochains (maximalSUnitsModule K Ω S)).X 1)
    (y : ∀ v : S, unitsModule (v.1.adicCompletion K) (AlgebraicClosure (v.1.adicCompletion K)))
    (hx : ((cochains (maximalSUnitsModule K Ω S)).d 1 2).hom x = 0)
    (hy : DataCond (localFamily ι S)
      (fun v : S => unitsModule (v.1.adicCompletion K) (AlgebraicClosure (v.1.adicCompletion K)))
      (fun v => sUnitsLocalHom ι S v.1) x y) :
    ∃ d : UnitsDatum Ω S, sInvCochainHom Ω S d = x ∧ dataLocalHom S ι d = y := by
  obtain ⟨T, hT⟩ := exists_coboundary_of_subsingleton (sUnitsToUnits S (maximalUnramifiedOutside K Ω S))
    (subsingleton_cohomology_one_unitsModule (K := K) (L := maximalUnramifiedOutside K Ω S)) x hx
  let t : sInvariantSubgroup Ω S := ⟨Additive.toMul T, toMul_mem_sInvariantSubgroup Ω S T x hT⟩
  have hxt : sInvCochain Ω S t = x := sInvCochain_eq_of Ω S t x hT
  have hinv : ∀ v : S, ∀ σ, (unitsModule (v.1.adicCompletion K)
      (AlgebraicClosure (v.1.adicCompletion K))).ρ σ (y v - sInvLocalHom S ι v.1 (Additive.ofMul t)) =
        y v - sInvLocalHom S ι v.1 (Additive.ofMul t) := fun v σ => by
    have e1 : (sUnitsLocalHom ι S v.1).hom (cochainOf (maximalSUnitsModule K Ω S) x
        ![(localFamily ι S v : _ →* GaloisGroupUnramifiedOutside K Ω S) σ]) =
        (unitsModule (v.1.adicCompletion K) (AlgebraicClosure (v.1.adicCompletion K))).ρ σ
          (sInvLocalHom S ι v.1 (Additive.ofMul t)) - sInvLocalHom S ι v.1 (Additive.ofMul t) := by
      rw [← hxt, cochainOf_sInvCochain, Matrix.cons_val_zero]
      exact sUnitsLocalHom_sInvRatio S ι v t σ
    have e := (hy v σ).symm.trans e1
    rw [map_sub]
    exact sub_eq_sub_iff_sub_eq_sub.mp e
  choose a ha using fun v : S => exists_localUnitsHom_eq v.1 _ (hinv v)
  exact ⟨(Additive.ofMul t, a), hxt, funext fun v =>
    (congrArg (· + sInvLocalHom S ι v.1 (Additive.ofMul t)) (ha v)).trans (sub_add_cancel _ _)⟩

/-- **Every class of `H_c¹(G_S, 𝒪_Sˣ)` comes from a datum** (Hilbert 90 for `K_Sˣ`). -/
theorem unitsData_surjective (ι : PlaceEmbeddings K Ω) : Function.Surjective (unitsData S ι) :=
  dataHom_surjective _ _ _ _ _ _ _ fun x y hx hy => exists_unitsDatum S ι x y hx hy

variable (Ω) in
/-- A unit of `K` as an `S`-invariant unit of `K_S`. -/
def sInvOfUnit (x : Kˣ) : sInvariantSubgroup Ω S :=
  ⟨_, map_algebraMap_mem_sInvariantSubgroup (Ω := Ω) S x⟩

variable (Ω) in
omit [IsSepClosure K Ω] in
theorem unitsModule_ρ_sInvOfUnit (x : Kˣ) (σ : GaloisGroupUnramifiedOutside K Ω S) :
    (unitsModule K (maximalUnramifiedOutside K Ω S)).ρ σ
        (Additive.ofMul ((sInvOfUnit Ω S x : sInvariantSubgroup Ω S) :
          (maximalUnramifiedOutside K Ω S)ˣ)) =
      Additive.ofMul ((sInvOfUnit Ω S x : sInvariantSubgroup Ω S) : (maximalUnramifiedOutside K Ω S)ˣ) :=
  Additive.toMul.injective (Units.ext (σ.commutes _))

theorem sInvLocalHom_sInvOfUnit (ι : PlaceEmbeddings K Ω) (x : Kˣ) (v : S) :
    sInvLocalHom S ι v.1 (Additive.ofMul (sInvOfUnit Ω S x)) =
      localUnitsHom v.1 (Additive.ofMul (Langlands.Global.finiteIdeleProjection K v.1 (Langlands.Global.diagonalUnits K x))) :=
  Additive.toMul.injective (Units.ext (((ι.finite v.1).commutes (x : K)).trans
    (IsScalarTower.algebraMap_apply K (v.1.adicCompletion K)
      (AlgebraicClosure (v.1.adicCompletion K)) (x : K))))

variable [Finite S]

variable (Ω) in
/-- **The `S`-idèle class of a datum** `(t, a)`: `sPresentation ((a_v)_v, -div(t))`. -/
def unitsClass : UnitsDatum Ω S →+ Additive (SIdeleClassGroup S) :=
  (MonoidHom.toAdditive (sPresentation S)).comp
    (AddMonoidHom.mk' (fun d => Additive.ofMul (fun w => Additive.toMul (d.2 w),
      Multiplicative.ofAdd (-divAbove S d.1))) fun d d' =>
        congrArg Additive.ofMul (Prod.ext rfl (congrArg Multiplicative.ofAdd
          ((congrArg Neg.neg (map_add (divAbove S) d.1 d'.1)).trans (neg_add _ _)))))

variable (Ω) in
theorem unitsClass_apply (d : UnitsDatum Ω S) :
    unitsClass Ω S d = Additive.ofMul (sPresentation S (fun w => Additive.toMul (d.2 w),
      Multiplicative.ofAdd (-divAbove S d.1))) :=
  rfl

variable (Ω) in
omit [Finite S] in
theorem mul_sInvOfUnit_mem_maximalSUnits (t : Additive (sInvariantSubgroup Ω S)) (x : Kˣ)
    (h : sDivisorOf S (Additive.ofMul x) = -divAbove S t) :
    ((Additive.toMul (t + Additive.ofMul (sInvOfUnit Ω S x)) : sInvariantSubgroup Ω S) :
      (maximalUnramifiedOutside K Ω S)ˣ) ∈ maximalSUnits K Ω S :=
  mem_maximalSUnits_of_divAbove_eq_zero S (((map_add (divAbove S) _ _).trans
    (congrArg (divAbove S t + ·) ((divAbove_algebraMap S x).trans h))).trans (add_neg_cancel _))

/-- `unitsData` vanishes on the data of `S`-idèle class zero. -/
theorem unitsData_eq_zero_of_unitsClass_eq_zero (ι : PlaceEmbeddings K Ω) (d : UnitsDatum Ω S)
    (h : unitsClass Ω S d = 0) : unitsData S ι d = 0 := by
  have h2 : ((fun w => Additive.toMul (d.2 w), Multiplicative.ofAdd (-divAbove S d.1)) :
      (∀ w : S, (Langlands.Global.FiniteCompletion K w.1)ˣ) × Multiplicative (SDivisor S)) ∈
      (principalPresentation S).range := by
    rw [← ker_sPresentation]
    exact congrArg Additive.toMul h
  obtain ⟨x, hx⟩ := h2
  have hx1 : ∀ w : S, Langlands.Global.finiteIdeleProjection K w.1 (Langlands.Global.diagonalUnits K x) =
      Additive.toMul (d.2 w) :=
    fun w => congrFun (congrArg Prod.fst hx) w
  have hx2 : sDivisorOf S (Additive.ofMul x) = -divAbove S d.1 :=
    congrArg Multiplicative.toAdd (congrArg Prod.snd hx)
  have hu := mul_sInvOfUnit_mem_maximalSUnits Ω S d.1 x hx2
  refine dataHom_eq_zero_of_boundary (localFamily ι S)
    (fun v : S => unitsModule (v.1.adicCompletion K) (AlgebraicClosure (v.1.adicCompletion K)))
    (fun v => sUnitsLocalHom ι S v.1) (sInvCochainHom Ω S) (dataLocalHom S ι)
    (fun d => d_sInvCochain Ω S _) (dataCond_unitsDatum S ι) d
    (Additive.ofMul ⟨_, hu⟩) (fun σ => ?_) (fun v => ?_)
  · refine sUnitsToUnits_injective S (maximalUnramifiedOutside K Ω S)
      ((sUnitsToUnits_sInvRatio Ω S _ σ).trans ?_)
    apply Additive.toMul.injective
    apply Units.ext
    change σ ((((Additive.toMul d.1 : sInvariantSubgroup Ω S) : (maximalUnramifiedOutside K Ω S)ˣ) :
        maximalUnramifiedOutside K Ω S)) *
        ((((Additive.toMul d.1 : sInvariantSubgroup Ω S) : (maximalUnramifiedOutside K Ω S)ˣ)⁻¹ :
          (maximalUnramifiedOutside K Ω S)ˣ) : maximalUnramifiedOutside K Ω S) =
      σ ((((Additive.toMul d.1 : sInvariantSubgroup Ω S) : (maximalUnramifiedOutside K Ω S)ˣ) :
          maximalUnramifiedOutside K Ω S) * algebraMap K _ (x : K)) *
        (((((Additive.toMul d.1 : sInvariantSubgroup Ω S) : (maximalUnramifiedOutside K Ω S)ˣ) *
          Units.map (algebraMap K (maximalUnramifiedOutside K Ω S) : K →* _) x)⁻¹ :
            (maximalUnramifiedOutside K Ω S)ˣ) : maximalUnramifiedOutside K Ω S)
    rw [map_mul, AlgEquiv.commutes, mul_inv, Units.val_mul]
    have hx0 : algebraMap K (maximalUnramifiedOutside K Ω S) (x : K) ≠ 0 :=
      (map_ne_zero _).2 x.ne_zero
    have hxi : (((Units.map (algebraMap K (maximalUnramifiedOutside K Ω S) : K →* _) x)⁻¹ :
        (maximalUnramifiedOutside K Ω S)ˣ) : maximalUnramifiedOutside K Ω S) =
        (algebraMap K (maximalUnramifiedOutside K Ω S) (x : K))⁻¹ := by
      rw [Units.val_inv_eq_inv_val]
      rfl
    rw [hxi, mul_mul_mul_comm, mul_inv_cancel₀ hx0, mul_one]
  · have e1 : localUnitsHom v.1 (d.2 v) =
        sInvLocalHom S ι v.1 (Additive.ofMul (sInvOfUnit Ω S x)) := by
      rw [sInvLocalHom_sInvOfUnit, hx1 v]
      rfl
    rw [dataLocalHom_apply, e1, ← map_add, add_comm]
    rfl

variable (Ω) in
/-- **Every `S`-idèle class is the class of a datum**: by the presentation of the `S`-idèle class
group and the principal ideal theorem (`divAbove_surjective`). -/
theorem unitsClass_surjective : Function.Surjective (unitsClass Ω S) := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  intro c
  obtain ⟨p, hp⟩ := sPresentation_surjective S (Additive.toMul c)
  obtain ⟨t, ht⟩ := divAbove_surjective (Ω := Ω) S (-(Multiplicative.toAdd p.2))
  refine ⟨(t, fun w => Additive.ofMul (p.1 w)), ?_⟩
  rw [unitsClass_apply, ht, neg_neg]
  exact congrArg Additive.ofMul hp

end Concrete

end

end Langlands.GaloisCohomology.PoitouTate.Internal
