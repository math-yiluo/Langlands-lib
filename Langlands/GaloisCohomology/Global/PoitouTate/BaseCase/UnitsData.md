# Classes of `H_c¹(G_S, 𝒪_Sˣ)` from `S`-invariant units and local units

`Langlands/GaloisCohomology/Global/PoitouTate/BaseCase/UnitsData.lean`, namespace `Langlands.GaloisCohomology.PoitouTate.Internal`.

With the notation of `Langlands.GaloisCohomology.Global.PoitouTate.BaseCase.Kummer`, a class of
`H_c¹(G_S, E; (K̄_vˣ)_{v ∈ S})` (`E = 𝒪_{K_S,S}ˣ`) is represented by a pair `(x, (y_v)_v)` of a
`1`-cocycle `x` of `G_S` with values in `E` and points `y_v ∈ K̄_vˣ` whose coboundaries are the
restrictions of `x` (the mapping cocone `mappingCoconeNat`: `d(x, y) = (dx, x|_{K_v} - dy)`).

**Data.** A *datum* (`UnitsDatum Ω S`) is a pair `(t, (a_v)_{v ∈ S})` of an `S`-invariant unit
`t ∈ K_Sˣ` (`t ∈ sInvariantSubgroup Ω S`: `σ(t)/t ∈ E` for all `σ ∈ G_S`) and local units
`a_v ∈ K_vˣ`, in additive notation. Its class `unitsData S ι d ∈ unitsCompact ι S 1` is the class of
the cocycle `(σ ↦ σ(t)/t, (ι_v(t) a_v)_v)`. In general (`dataCochain`, `dataCycle`, `dataHom`,
`DataCond`), for any family of local groups and local coefficient maps, a `0`-cochain `c` of the
global module with a family of local points `p_v` with `d(c|_v) = d p_v` gives a cycle of the mapping
cocone; `dataHom` is additive, surjective when the global and local `H¹` vanish in the right way
(`dataHom_surjective`), zero on boundaries (`dataHom_eq_zero_of_boundary`), and on data with `c`
invariant it is `localToCompact` of the local classes (`dataHom_eq_localToCompact`).

**Main statements.**
* `unitsData_surjective`: every class of `H_c¹(G_S, E; (K̄_vˣ)_v)` comes from a datum (Hilbert 90 for
  `K_Sˣ` and the local fields: a `1`-cocycle in `E` is `σ ↦ σ(t)/t` for some `t ∈ K_Sˣ`, which is then
  `S`-invariant).
* `unitsData_zero_left`: on data `(1, a)`, `unitsData` is `localToCompact` of the classes `a_v` in
  `H⁰(K_v, K̄_vˣ)`.
* `unitsClass Ω S : UnitsDatum Ω S →+ Additive (SIdeleClassGroup S)`, `d ↦ sPresentation(a, -div(t))`
  (`divAbove S t`, the divisor of `t` prime to `S`); it is surjective (`unitsClass_surjective`, from
  `divAbove_surjective` and `sPresentation_surjective`).
* `unitsData_eq_zero_of_unitsClass_eq_zero`: `unitsData` vanishes on the data of class zero.

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.PoitouTate.Internal.piConst.{u} {k : Type u} [CommRing k] {ι : Type u} {H : ι → Type u}
  [(v : ι) → Group (H v)] [(v : ι) → TopologicalSpace (H v)] [∀ (v : ι), IsTopologicalGroup (H v)]
  (Ωᵥ : (v : ι) → Rep.{u, u, u} k (H v)) [∀ (v : ι), Langlands.IsSmoothRep (Ωᵥ v)] (y : (v : ι) → ↑(Ωᵥ v)) :
  ↑((Langlands.GaloisCohomology.piComplex fun v => Langlands.ProfiniteCohomology.cochains (Ωᵥ v)).X 0)
Langlands.GaloisCohomology.PoitouTate.Internal.piConst_apply.{u} {k : Type u} [CommRing k] {ι : Type u} {H : ι → Type u}
  [(v : ι) → Group (H v)] [(v : ι) → TopologicalSpace (H v)] [∀ (v : ι), IsTopologicalGroup (H v)]
  (Ωᵥ : (v : ι) → Rep.{u, u, u} k (H v)) [∀ (v : ι), Langlands.IsSmoothRep (Ωᵥ v)] (y : (v : ι) → ↑(Ωᵥ v)) (v : ι) :
  Langlands.GaloisCohomology.PoitouTate.Internal.piConst Ωᵥ y v = (Langlands.GaloisCohomology.zeroCochain (Ωᵥ v)) (y v)
Langlands.GaloisCohomology.PoitouTate.Internal.piConst_add.{u} {k : Type u} [CommRing k] {ι : Type u} {H : ι → Type u}
  [(v : ι) → Group (H v)] [(v : ι) → TopologicalSpace (H v)] [∀ (v : ι), IsTopologicalGroup (H v)]
  (Ωᵥ : (v : ι) → Rep.{u, u, u} k (H v)) [∀ (v : ι), Langlands.IsSmoothRep (Ωᵥ v)] (y y' : (v : ι) → ↑(Ωᵥ v)) :
  Langlands.GaloisCohomology.PoitouTate.Internal.piConst Ωᵥ (y + y') =
    Langlands.GaloisCohomology.PoitouTate.Internal.piConst Ωᵥ y +
      Langlands.GaloisCohomology.PoitouTate.Internal.piConst Ωᵥ y'
Langlands.GaloisCohomology.PoitouTate.Internal.DataCond.{u} {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {ι : Type u} {H : ι → Type u} [(v : ι) → Group (H v)] [(v : ι) → TopologicalSpace (H v)]
  (φ : (v : ι) → H v →ₜ* G) {U : Rep.{u, u, u} k G} [Langlands.IsSmoothRep U] (Ωᵥ : (v : ι) → Rep.{u, u, u} k (H v))
  (a : (v : ι) → Rep.res (↑(φ v)) U ⟶ Ωᵥ v) (x : ↑((Langlands.ProfiniteCohomology.cochains U).X 1))
  (y : (v : ι) → ↑(Ωᵥ v)) : Prop
Langlands.GaloisCohomology.PoitouTate.Internal.dataCochain.{u} {k G : Type u} [CommRing k] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] {ι : Type u} {H : ι → Type u} [(v : ι) → Group (H v)]
  [(v : ι) → TopologicalSpace (H v)] [∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G)
  {U : Rep.{u, u, u} k G} [Langlands.IsSmoothRep U] (Ωᵥ : (v : ι) → Rep.{u, u, u} k (H v))
  [∀ (v : ι), Langlands.IsSmoothRep (Ωᵥ v)] (a : (v : ι) → Rep.res (↑(φ v)) U ⟶ Ωᵥ v)
  (x : ↑((Langlands.ProfiniteCohomology.cochains U).X 1)) (y : (v : ι) → ↑(Ωᵥ v)) :
  ↑((Langlands.GaloisCohomology.compactSupportCochains φ U Ωᵥ a).X 1)
Langlands.GaloisCohomology.PoitouTate.Internal.dataCochain_add.{u} {k G : Type u} [CommRing k] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] {ι : Type u} {H : ι → Type u} [(v : ι) → Group (H v)]
  [(v : ι) → TopologicalSpace (H v)] [∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G)
  {U : Rep.{u, u, u} k G} [Langlands.IsSmoothRep U] (Ωᵥ : (v : ι) → Rep.{u, u, u} k (H v))
  [∀ (v : ι), Langlands.IsSmoothRep (Ωᵥ v)] (a : (v : ι) → Rep.res (↑(φ v)) U ⟶ Ωᵥ v)
  (x x' : ↑((Langlands.ProfiniteCohomology.cochains U).X 1)) (y y' : (v : ι) → ↑(Ωᵥ v)) :
  Langlands.GaloisCohomology.PoitouTate.Internal.dataCochain φ Ωᵥ a (x + x') (y + y') =
    Langlands.GaloisCohomology.PoitouTate.Internal.dataCochain φ Ωᵥ a x y +
      Langlands.GaloisCohomology.PoitouTate.Internal.dataCochain φ Ωᵥ a x' y'
Langlands.GaloisCohomology.PoitouTate.Internal.localRes_one_eq_d_piConst.{u} {k G : Type u} [CommRing k] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] {ι : Type u} {H : ι → Type u} [(v : ι) → Group (H v)]
  [(v : ι) → TopologicalSpace (H v)] [∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G)
  {U : Rep.{u, u, u} k G} [Langlands.IsSmoothRep U] (Ωᵥ : (v : ι) → Rep.{u, u, u} k (H v))
  [∀ (v : ι), Langlands.IsSmoothRep (Ωᵥ v)] (a : (v : ι) → Rep.res (↑(φ v)) U ⟶ Ωᵥ v)
  (x : ↑((Langlands.ProfiniteCohomology.cochains U).X 1)) (y : (v : ι) → ↑(Ωᵥ v))
  (hy : Langlands.GaloisCohomology.PoitouTate.Internal.DataCond φ Ωᵥ a x y) :
  (ModuleCat.Hom.hom ((Langlands.GaloisCohomology.localRes φ U Ωᵥ a).f (0 + 1))) x =
    (ModuleCat.Hom.hom
        ((Langlands.GaloisCohomology.piComplex fun v => Langlands.ProfiniteCohomology.cochains (Ωᵥ v)).d 0 (0 + 1)))
      (Langlands.GaloisCohomology.PoitouTate.Internal.piConst Ωᵥ y)
Langlands.GaloisCohomology.PoitouTate.Internal.d_dataCochain.{u} {k G : Type u} [CommRing k] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] {ι : Type u} {H : ι → Type u} [(v : ι) → Group (H v)]
  [(v : ι) → TopologicalSpace (H v)] [∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G)
  {U : Rep.{u, u, u} k G} [Langlands.IsSmoothRep U] (Ωᵥ : (v : ι) → Rep.{u, u, u} k (H v))
  [∀ (v : ι), Langlands.IsSmoothRep (Ωᵥ v)] (a : (v : ι) → Rep.res (↑(φ v)) U ⟶ Ωᵥ v)
  (x : ↑((Langlands.ProfiniteCohomology.cochains U).X 1)) (y : (v : ι) → ↑(Ωᵥ v))
  (hx : (ModuleCat.Hom.hom ((Langlands.ProfiniteCohomology.cochains U).d 1 2)) x = 0)
  (hy : Langlands.GaloisCohomology.PoitouTate.Internal.DataCond φ Ωᵥ a x y) :
  (ModuleCat.Hom.hom ((Langlands.GaloisCohomology.compactSupportCochains φ U Ωᵥ a).d 1 2))
      (Langlands.GaloisCohomology.PoitouTate.Internal.dataCochain φ Ωᵥ a x y) =
    0
Langlands.GaloisCohomology.PoitouTate.Internal.dataCycle.{u} {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {ι : Type u} {H : ι → Type u} [(v : ι) → Group (H v)] [(v : ι) → TopologicalSpace (H v)]
  [∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G) {U : Rep.{u, u, u} k G} [Langlands.IsSmoothRep U]
  (Ωᵥ : (v : ι) → Rep.{u, u, u} k (H v)) [∀ (v : ι), Langlands.IsSmoothRep (Ωᵥ v)]
  (a : (v : ι) → Rep.res (↑(φ v)) U ⟶ Ωᵥ v) (x : ↑((Langlands.ProfiniteCohomology.cochains U).X 1))
  (y : (v : ι) → ↑(Ωᵥ v)) (hx : (ModuleCat.Hom.hom ((Langlands.ProfiniteCohomology.cochains U).d 1 2)) x = 0)
  (hy : Langlands.GaloisCohomology.PoitouTate.Internal.DataCond φ Ωᵥ a x y) :
  ↑(HomologicalComplex.cycles (Langlands.GaloisCohomology.compactSupportCochains φ U Ωᵥ a) 1)
Langlands.GaloisCohomology.PoitouTate.Internal.iCycles_dataCycle.{u} {k G : Type u} [CommRing k] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] {ι : Type u} {H : ι → Type u} [(v : ι) → Group (H v)]
  [(v : ι) → TopologicalSpace (H v)] [∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G)
  {U : Rep.{u, u, u} k G} [Langlands.IsSmoothRep U] (Ωᵥ : (v : ι) → Rep.{u, u, u} k (H v))
  [∀ (v : ι), Langlands.IsSmoothRep (Ωᵥ v)] (a : (v : ι) → Rep.res (↑(φ v)) U ⟶ Ωᵥ v)
  (x : ↑((Langlands.ProfiniteCohomology.cochains U).X 1)) (y : (v : ι) → ↑(Ωᵥ v))
  (hx : (ModuleCat.Hom.hom ((Langlands.ProfiniteCohomology.cochains U).d 1 2)) x = 0)
  (hy : Langlands.GaloisCohomology.PoitouTate.Internal.DataCond φ Ωᵥ a x y) :
  (ModuleCat.Hom.hom (HomologicalComplex.iCycles (Langlands.GaloisCohomology.compactSupportCochains φ U Ωᵥ a) 1))
      (Langlands.GaloisCohomology.PoitouTate.Internal.dataCycle φ Ωᵥ a x y hx hy) =
    Langlands.GaloisCohomology.PoitouTate.Internal.dataCochain φ Ωᵥ a x y
Langlands.GaloisCohomology.PoitouTate.Internal.dataCycle_congr.{u} {k G : Type u} [CommRing k] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] {ι : Type u} {H : ι → Type u} [(v : ι) → Group (H v)]
  [(v : ι) → TopologicalSpace (H v)] [∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G)
  {U : Rep.{u, u, u} k G} [Langlands.IsSmoothRep U] (Ωᵥ : (v : ι) → Rep.{u, u, u} k (H v))
  [∀ (v : ι), Langlands.IsSmoothRep (Ωᵥ v)] (a : (v : ι) → Rep.res (↑(φ v)) U ⟶ Ωᵥ v)
  {x x' : ↑((Langlands.ProfiniteCohomology.cochains U).X 1)} {y y' : (v : ι) → ↑(Ωᵥ v)} (ex : x = x') (ey : y = y')
  (hx : (ModuleCat.Hom.hom ((Langlands.ProfiniteCohomology.cochains U).d 1 2)) x = 0)
  (hx' : (ModuleCat.Hom.hom ((Langlands.ProfiniteCohomology.cochains U).d 1 2)) x' = 0)
  (hy : Langlands.GaloisCohomology.PoitouTate.Internal.DataCond φ Ωᵥ a x y)
  (hy' : Langlands.GaloisCohomology.PoitouTate.Internal.DataCond φ Ωᵥ a x' y') :
  Langlands.GaloisCohomology.PoitouTate.Internal.dataCycle φ Ωᵥ a x y hx hy =
    Langlands.GaloisCohomology.PoitouTate.Internal.dataCycle φ Ωᵥ a x' y' hx' hy'
Langlands.GaloisCohomology.PoitouTate.Internal.dataCond_add.{u} {k G : Type u} [CommRing k] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] {ι : Type u} {H : ι → Type u} [(v : ι) → Group (H v)]
  [(v : ι) → TopologicalSpace (H v)] (φ : (v : ι) → H v →ₜ* G) {U : Rep.{u, u, u} k G} [Langlands.IsSmoothRep U]
  (Ωᵥ : (v : ι) → Rep.{u, u, u} k (H v)) (a : (v : ι) → Rep.res (↑(φ v)) U ⟶ Ωᵥ v)
  {x x' : ↑((Langlands.ProfiniteCohomology.cochains U).X 1)} {y y' : (v : ι) → ↑(Ωᵥ v)}
  (hy : Langlands.GaloisCohomology.PoitouTate.Internal.DataCond φ Ωᵥ a x y)
  (hy' : Langlands.GaloisCohomology.PoitouTate.Internal.DataCond φ Ωᵥ a x' y') :
  Langlands.GaloisCohomology.PoitouTate.Internal.DataCond φ Ωᵥ a (x + x') (y + y')
Langlands.GaloisCohomology.PoitouTate.Internal.dataCond_zero.{u} {k G : Type u} [CommRing k] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] {ι : Type u} {H : ι → Type u} [(v : ι) → Group (H v)]
  [(v : ι) → TopologicalSpace (H v)] (φ : (v : ι) → H v →ₜ* G) {U : Rep.{u, u, u} k G} [Langlands.IsSmoothRep U]
  (Ωᵥ : (v : ι) → Rep.{u, u, u} k (H v)) (a : (v : ι) → Rep.res (↑(φ v)) U ⟶ Ωᵥ v) :
  Langlands.GaloisCohomology.PoitouTate.Internal.DataCond φ Ωᵥ a 0 0
Langlands.GaloisCohomology.PoitouTate.Internal.dataHom.{u} {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {ι : Type u} {H : ι → Type u} [(v : ι) → Group (H v)] [(v : ι) → TopologicalSpace (H v)]
  [∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G) {U : Rep.{u, u, u} k G} [Langlands.IsSmoothRep U]
  (Ωᵥ : (v : ι) → Rep.{u, u, u} k (H v)) [∀ (v : ι), Langlands.IsSmoothRep (Ωᵥ v)]
  (a : (v : ι) → Rep.res (↑(φ v)) U ⟶ Ωᵥ v) {D : Type u} [AddCommGroup D]
  (xOf : D →+ ↑((Langlands.ProfiniteCohomology.cochains U).X 1)) (yOf : D →+ (v : ι) → ↑(Ωᵥ v))
  (hx : ∀ (d : D), (ModuleCat.Hom.hom ((Langlands.ProfiniteCohomology.cochains U).d 1 2)) (xOf d) = 0)
  (hy : ∀ (d : D), Langlands.GaloisCohomology.PoitouTate.Internal.DataCond φ Ωᵥ a (xOf d) (yOf d)) :
  D →+ ↑(Langlands.GaloisCohomology.compactSupportCohomology φ U Ωᵥ a 1)
Langlands.GaloisCohomology.PoitouTate.Internal.dataHom_apply.{u} {k G : Type u} [CommRing k] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] {ι : Type u} {H : ι → Type u} [(v : ι) → Group (H v)]
  [(v : ι) → TopologicalSpace (H v)] [∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G)
  {U : Rep.{u, u, u} k G} [Langlands.IsSmoothRep U] (Ωᵥ : (v : ι) → Rep.{u, u, u} k (H v))
  [∀ (v : ι), Langlands.IsSmoothRep (Ωᵥ v)] (a : (v : ι) → Rep.res (↑(φ v)) U ⟶ Ωᵥ v) {D : Type u} [AddCommGroup D]
  (xOf : D →+ ↑((Langlands.ProfiniteCohomology.cochains U).X 1)) (yOf : D →+ (v : ι) → ↑(Ωᵥ v))
  (hx : ∀ (d : D), (ModuleCat.Hom.hom ((Langlands.ProfiniteCohomology.cochains U).d 1 2)) (xOf d) = 0)
  (hy : ∀ (d : D), Langlands.GaloisCohomology.PoitouTate.Internal.DataCond φ Ωᵥ a (xOf d) (yOf d)) (d : D) :
  (Langlands.GaloisCohomology.PoitouTate.Internal.dataHom φ Ωᵥ a xOf yOf hx hy) d =
    (ModuleCat.Hom.hom (HomologicalComplex.homologyπ (Langlands.GaloisCohomology.compactSupportCochains φ U Ωᵥ a) 1))
      (Langlands.GaloisCohomology.PoitouTate.Internal.dataCycle φ Ωᵥ a (xOf d) (yOf d) ⋯ ⋯)
Langlands.GaloisCohomology.PoitouTate.Internal.exists_dataCycle_eq.{u} {k G : Type u} [CommRing k] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] {ι : Type u} {H : ι → Type u} [(v : ι) → Group (H v)]
  [(v : ι) → TopologicalSpace (H v)] [∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G)
  {U : Rep.{u, u, u} k G} [Langlands.IsSmoothRep U] (Ωᵥ : (v : ι) → Rep.{u, u, u} k (H v))
  [∀ (v : ι), Langlands.IsSmoothRep (Ωᵥ v)] (a : (v : ι) → Rep.res (↑(φ v)) U ⟶ Ωᵥ v)
  (c : ↑(HomologicalComplex.cycles (Langlands.GaloisCohomology.compactSupportCochains φ U Ωᵥ a) 1)) :
  ∃ x y,
    ∃ (hx : (ModuleCat.Hom.hom ((Langlands.ProfiniteCohomology.cochains U).d 1 2)) x = 0) (hy :
      Langlands.GaloisCohomology.PoitouTate.Internal.DataCond φ Ωᵥ a x y),
      c = Langlands.GaloisCohomology.PoitouTate.Internal.dataCycle φ Ωᵥ a x y hx hy
Langlands.GaloisCohomology.PoitouTate.Internal.dataHom_surjective.{u} {k G : Type u} [CommRing k] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] {ι : Type u} {H : ι → Type u} [(v : ι) → Group (H v)]
  [(v : ι) → TopologicalSpace (H v)] [∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G)
  {U : Rep.{u, u, u} k G} [Langlands.IsSmoothRep U] (Ωᵥ : (v : ι) → Rep.{u, u, u} k (H v))
  [∀ (v : ι), Langlands.IsSmoothRep (Ωᵥ v)] (a : (v : ι) → Rep.res (↑(φ v)) U ⟶ Ωᵥ v) {D : Type u} [AddCommGroup D]
  (xOf : D →+ ↑((Langlands.ProfiniteCohomology.cochains U).X 1)) (yOf : D →+ (v : ι) → ↑(Ωᵥ v))
  (hx : ∀ (d : D), (ModuleCat.Hom.hom ((Langlands.ProfiniteCohomology.cochains U).d 1 2)) (xOf d) = 0)
  (hy : ∀ (d : D), Langlands.GaloisCohomology.PoitouTate.Internal.DataCond φ Ωᵥ a (xOf d) (yOf d))
  (hd :
    ∀ (x : ↑((Langlands.ProfiniteCohomology.cochains U).X 1)) (y : (v : ι) → ↑(Ωᵥ v)),
      (ModuleCat.Hom.hom ((Langlands.ProfiniteCohomology.cochains U).d 1 2)) x = 0 →
        Langlands.GaloisCohomology.PoitouTate.Internal.DataCond φ Ωᵥ a x y → ∃ d, xOf d = x ∧ yOf d = y) :
  Function.Surjective ⇑(Langlands.GaloisCohomology.PoitouTate.Internal.dataHom φ Ωᵥ a xOf yOf hx hy)
Langlands.GaloisCohomology.PoitouTate.Internal.homologyπ_dataCycle_of_boundary.{u} {k G : Type u} [CommRing k] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] {ι : Type u} {H : ι → Type u} [(v : ι) → Group (H v)]
  [(v : ι) → TopologicalSpace (H v)] [∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G)
  {U : Rep.{u, u, u} k G} [Langlands.IsSmoothRep U] (Ωᵥ : (v : ι) → Rep.{u, u, u} k (H v))
  [∀ (v : ι), Langlands.IsSmoothRep (Ωᵥ v)] (a : (v : ι) → Rep.res (↑(φ v)) U ⟶ Ωᵥ v) (α : ↑U)
  (x : ↑((Langlands.ProfiniteCohomology.cochains U).X 1)) (y : (v : ι) → ↑(Ωᵥ v))
  (hx : (ModuleCat.Hom.hom ((Langlands.ProfiniteCohomology.cochains U).d 1 2)) x = 0)
  (hy : Langlands.GaloisCohomology.PoitouTate.Internal.DataCond φ Ωᵥ a x y)
  (hxα : ∀ (σ : G), Langlands.ProfiniteCohomology.cochainOf U x ![σ] = (U.ρ σ) α - α)
  (hyα : ∀ (v : ι), y v = (Rep.Hom.hom (a v)) α) :
  (ModuleCat.Hom.hom (HomologicalComplex.homologyπ (Langlands.GaloisCohomology.compactSupportCochains φ U Ωᵥ a) 1))
      (Langlands.GaloisCohomology.PoitouTate.Internal.dataCycle φ Ωᵥ a x y hx hy) =
    0
Langlands.GaloisCohomology.PoitouTate.Internal.dataHom_eq_zero_of_boundary.{u} {k G : Type u} [CommRing k] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] {ι : Type u} {H : ι → Type u} [(v : ι) → Group (H v)]
  [(v : ι) → TopologicalSpace (H v)] [∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G)
  {U : Rep.{u, u, u} k G} [Langlands.IsSmoothRep U] (Ωᵥ : (v : ι) → Rep.{u, u, u} k (H v))
  [∀ (v : ι), Langlands.IsSmoothRep (Ωᵥ v)] (a : (v : ι) → Rep.res (↑(φ v)) U ⟶ Ωᵥ v) {D : Type u} [AddCommGroup D]
  (xOf : D →+ ↑((Langlands.ProfiniteCohomology.cochains U).X 1)) (yOf : D →+ (v : ι) → ↑(Ωᵥ v))
  (hx : ∀ (d : D), (ModuleCat.Hom.hom ((Langlands.ProfiniteCohomology.cochains U).d 1 2)) (xOf d) = 0)
  (hy : ∀ (d : D), Langlands.GaloisCohomology.PoitouTate.Internal.DataCond φ Ωᵥ a (xOf d) (yOf d)) (d : D) (α : ↑U)
  (hxα : ∀ (σ : G), Langlands.ProfiniteCohomology.cochainOf U (xOf d) ![σ] = (U.ρ σ) α - α)
  (hyα : ∀ (v : ι), yOf d v = (Rep.Hom.hom (a v)) α) :
  (Langlands.GaloisCohomology.PoitouTate.Internal.dataHom φ Ωᵥ a xOf yOf hx hy) d = 0
Langlands.GaloisCohomology.PoitouTate.Internal.exists_coboundary_of_subsingleton.{u} {k G : Type u} [CommRing k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {U : Rep.{u, u, u} k G} [Langlands.IsSmoothRep U]
  {X : Rep.{u, u, u} k G} [Langlands.IsSmoothRep X] (j : U ⟶ X)
  (hX : Subsingleton ↑(Langlands.ProfiniteCohomology.cohomology X 1))
  (x : ↑((Langlands.ProfiniteCohomology.cochains U).X 1))
  (hx : (ModuleCat.Hom.hom ((Langlands.ProfiniteCohomology.cochains U).d 1 2)) x = 0) :
  ∃ T, ∀ (σ : G), (Rep.Hom.hom j) (Langlands.ProfiniteCohomology.cochainOf U x ![σ]) = (X.ρ σ) T - T
Langlands.GaloisCohomology.PoitouTate.Internal.homologyπ_dataCycle_zero_of_invariant.{u} {k G : Type u} [CommRing k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {ι : Type u} {H : ι → Type u} [(v : ι) → Group (H v)]
  [(v : ι) → TopologicalSpace (H v)] [∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G)
  {U : Rep.{u, u, u} k G} [Langlands.IsSmoothRep U] (Ωᵥ : (v : ι) → Rep.{u, u, u} k (H v))
  [∀ (v : ι), Langlands.IsSmoothRep (Ωᵥ v)] (a : (v : ι) → Rep.res (↑(φ v)) U ⟶ Ωᵥ v) (y : (v : ι) → ↑(Ωᵥ v))
  (hy0 : ∀ (v : ι) (σ : H v), ((Ωᵥ v).ρ σ) (y v) = y v)
  (hx : (ModuleCat.Hom.hom ((Langlands.ProfiniteCohomology.cochains U).d 1 2)) 0 = 0)
  (hy : Langlands.GaloisCohomology.PoitouTate.Internal.DataCond φ Ωᵥ a 0 y) :
  (ModuleCat.Hom.hom (HomologicalComplex.homologyπ (Langlands.GaloisCohomology.compactSupportCochains φ U Ωᵥ a) 1))
      (Langlands.GaloisCohomology.PoitouTate.Internal.dataCycle φ Ωᵥ a 0 y hx hy) =
    (ModuleCat.Hom.hom (Langlands.GaloisCohomology.localToCompact φ U Ωᵥ a 0)) fun v =>
      (ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.zeroIso (Ωᵥ v)).inv) ⟨y v, ⋯⟩
Langlands.GaloisCohomology.PoitouTate.Internal.dataHom_eq_localToCompact.{u} {k G : Type u} [CommRing k] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] {ι : Type u} {H : ι → Type u} [(v : ι) → Group (H v)]
  [(v : ι) → TopologicalSpace (H v)] [∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G)
  {U : Rep.{u, u, u} k G} [Langlands.IsSmoothRep U] (Ωᵥ : (v : ι) → Rep.{u, u, u} k (H v))
  [∀ (v : ι), Langlands.IsSmoothRep (Ωᵥ v)] (a : (v : ι) → Rep.res (↑(φ v)) U ⟶ Ωᵥ v) {D : Type u} [AddCommGroup D]
  (xOf : D →+ ↑((Langlands.ProfiniteCohomology.cochains U).X 1)) (yOf : D →+ (v : ι) → ↑(Ωᵥ v))
  (hx : ∀ (d : D), (ModuleCat.Hom.hom ((Langlands.ProfiniteCohomology.cochains U).d 1 2)) (xOf d) = 0)
  (hy : ∀ (d : D), Langlands.GaloisCohomology.PoitouTate.Internal.DataCond φ Ωᵥ a (xOf d) (yOf d)) (d : D)
  (hx0 : xOf d = 0) (y : (v : ι) → ↑(Ωᵥ v)) (hyd : yOf d = y) (hy0 : ∀ (v : ι) (σ : H v), ((Ωᵥ v).ρ σ) (y v) = y v) :
  (Langlands.GaloisCohomology.PoitouTate.Internal.dataHom φ Ωᵥ a xOf yOf hx hy) d =
    (ModuleCat.Hom.hom (Langlands.GaloisCohomology.localToCompact φ U Ωᵥ a 0)) fun v =>
      (ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.zeroIso (Ωᵥ v)).inv) ⟨y v, ⋯⟩
Langlands.GaloisCohomology.PoitouTate.Internal.sInvRatio.{u} {K : Type u} [Field K] [NumberField K] (Ω : Type u)
  [Field Ω] [Algebra K Ω] (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (t : ↥(Langlands.GaloisCohomology.sInvariantSubgroup Ω S)) (σ : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) :
  Additive ↥(Langlands.GaloisCohomology.maximalSUnits K Ω S)
Langlands.GaloisCohomology.PoitouTate.Internal.sUnitsToUnits_sInvRatio.{u} {K : Type u} [Field K] [NumberField K]
  (Ω : Type u) [Field Ω] [Algebra K Ω] (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (t : ↥(Langlands.GaloisCohomology.sInvariantSubgroup Ω S)) (σ : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) :
  (Rep.Hom.hom (Langlands.GaloisCohomology.sUnitsToUnits S ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)))
      (Langlands.GaloisCohomology.PoitouTate.Internal.sInvRatio Ω S t σ) =
    ((Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)).ρ σ)
        (Additive.ofMul ↑t) -
      have this := Additive.ofMul ↑t;
      this
Langlands.GaloisCohomology.PoitouTate.Internal.sInvRatio_mul.{u} {K : Type u} [Field K] [NumberField K] (Ω : Type u)
  [Field Ω] [Algebra K Ω] (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (t t' : ↥(Langlands.GaloisCohomology.sInvariantSubgroup Ω S))
  (σ : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) :
  Langlands.GaloisCohomology.PoitouTate.Internal.sInvRatio Ω S (t * t') σ =
    Langlands.GaloisCohomology.PoitouTate.Internal.sInvRatio Ω S t σ +
      Langlands.GaloisCohomology.PoitouTate.Internal.sInvRatio Ω S t' σ
Langlands.GaloisCohomology.PoitouTate.Internal.isLocallyConstant_sInvRatio.{u} {K : Type u} [Field K] [NumberField K]
  (Ω : Type u) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (t : ↥(Langlands.GaloisCohomology.sInvariantSubgroup Ω S)) :
  IsLocallyConstant (Langlands.GaloisCohomology.PoitouTate.Internal.sInvRatio Ω S t)
Langlands.GaloisCohomology.PoitouTate.Internal.sInvCochain.{u} {K : Type u} [Field K] [NumberField K] (Ω : Type u)
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (t : ↥(Langlands.GaloisCohomology.sInvariantSubgroup Ω S)) :
  ↑((Langlands.ProfiniteCohomology.cochains (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S)).X 1)
Langlands.GaloisCohomology.PoitouTate.Internal.cochainOf_sInvCochain.{u} {K : Type u} [Field K] [NumberField K]
  (Ω : Type u) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (t : ↥(Langlands.GaloisCohomology.sInvariantSubgroup Ω S))
  (σ : Fin 1 → Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) :
  Langlands.ProfiniteCohomology.cochainOf (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S)
      (Langlands.GaloisCohomology.PoitouTate.Internal.sInvCochain Ω S t) σ =
    Langlands.GaloisCohomology.PoitouTate.Internal.sInvRatio Ω S t (σ 0)
Langlands.GaloisCohomology.PoitouTate.Internal.sInvCochain_mul.{u} {K : Type u} [Field K] [NumberField K] (Ω : Type u)
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (t t' : ↥(Langlands.GaloisCohomology.sInvariantSubgroup Ω S)) :
  Langlands.GaloisCohomology.PoitouTate.Internal.sInvCochain Ω S (t * t') =
    Langlands.GaloisCohomology.PoitouTate.Internal.sInvCochain Ω S t +
      Langlands.GaloisCohomology.PoitouTate.Internal.sInvCochain Ω S t'
Langlands.GaloisCohomology.PoitouTate.Internal.sInvCochain_one.{u} {K : Type u} [Field K] [NumberField K] (Ω : Type u)
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) :
  Langlands.GaloisCohomology.PoitouTate.Internal.sInvCochain Ω S 1 = 0
Langlands.GaloisCohomology.PoitouTate.Internal.cochainsMap_sUnitsToUnits_sInvCochain.{u} {K : Type u} [Field K]
  [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (t : ↥(Langlands.GaloisCohomology.sInvariantSubgroup Ω S)) :
  (CategoryTheory.ConcreteCategory.hom
        ((Langlands.ProfiniteCohomology.coeffCochainsMap
              (Langlands.GaloisCohomology.sUnitsToUnits S ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))).f
          1))
      (Langlands.GaloisCohomology.PoitouTate.Internal.sInvCochain Ω S t) =
    (ModuleCat.Hom.hom
        ((Langlands.ProfiniteCohomology.cochains
              (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))).d
          0 1))
      ((Langlands.GaloisCohomology.zeroCochain
          (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)))
        (Additive.ofMul ↑t))
Langlands.GaloisCohomology.PoitouTate.Internal.d_sInvCochain.{u} {K : Type u} [Field K] [NumberField K] (Ω : Type u)
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (t : ↥(Langlands.GaloisCohomology.sInvariantSubgroup Ω S)) :
  (ModuleCat.Hom.hom
        ((Langlands.ProfiniteCohomology.cochains (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S)).d 1 2))
      (Langlands.GaloisCohomology.PoitouTate.Internal.sInvCochain Ω S t) =
    0
Langlands.GaloisCohomology.PoitouTate.Internal.localUnitsHom.{u} {K : Type u} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
  Additive (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)ˣ →+
    ↑(Langlands.GaloisCohomology.unitsModule (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)))
Langlands.GaloisCohomology.PoitouTate.Internal.sInvLocalHom.{u} {K : Type u} [Field K] [NumberField K] {Ω : Type u}
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
  Additive ↥(Langlands.GaloisCohomology.sInvariantSubgroup Ω S) →+
    ↑(Langlands.GaloisCohomology.unitsModule (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)))
Langlands.GaloisCohomology.PoitouTate.Internal.localUnitsHom_invariant.{u} {K : Type u} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (σ :
    Gal(AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)/IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
  (a : Additive (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)ˣ) :
  ((Langlands.GaloisCohomology.unitsModule (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
            (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))).ρ
        σ)
      ((Langlands.GaloisCohomology.PoitouTate.Internal.localUnitsHom v) a) =
    (Langlands.GaloisCohomology.PoitouTate.Internal.localUnitsHom v) a
Langlands.GaloisCohomology.PoitouTate.Internal.UnitsDatum.{u} {K : Type u} [Field K] [NumberField K] (Ω : Type u)
  [Field Ω] [Algebra K Ω] (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) : Type u
Langlands.GaloisCohomology.PoitouTate.Internal.dataLocalHom.{u} {K : Type u} [Field K] [NumberField K] {Ω : Type u}
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) :
  Langlands.GaloisCohomology.PoitouTate.Internal.UnitsDatum Ω S →+
    (v : ↑S) →
      ↑(Langlands.GaloisCohomology.unitsModule (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)))
Langlands.GaloisCohomology.PoitouTate.Internal.dataLocalHom_apply.{u} {K : Type u} [Field K] [NumberField K]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (d : Langlands.GaloisCohomology.PoitouTate.Internal.UnitsDatum Ω S)
  (v : ↑S) :
  (Langlands.GaloisCohomology.PoitouTate.Internal.dataLocalHom S ι) d v =
    (Langlands.GaloisCohomology.PoitouTate.Internal.localUnitsHom ↑v) (d.2 v) +
      (Langlands.GaloisCohomology.PoitouTate.Internal.sInvLocalHom S ι ↑v) d.1
Langlands.GaloisCohomology.PoitouTate.Internal.sInvCochainHom.{u} {K : Type u} [Field K] [NumberField K] (Ω : Type u)
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) :
  Langlands.GaloisCohomology.PoitouTate.Internal.UnitsDatum Ω S →+
    ↑((Langlands.ProfiniteCohomology.cochains (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S)).X 1)
Langlands.GaloisCohomology.PoitouTate.Internal.sUnitsLocalHom_sInvRatio.{u} {K : Type u} [Field K] [NumberField K]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (v : ↑S) (t : ↥(Langlands.GaloisCohomology.sInvariantSubgroup Ω S))
  (σ :
    Gal(AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion K
          ↑v)/IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)) :
  (Rep.Hom.hom (Langlands.GaloisCohomology.PoitouTate.Internal.sUnitsLocalHom ι S ↑v))
      (Langlands.GaloisCohomology.PoitouTate.Internal.sInvRatio Ω S t
        (↑(Langlands.GaloisCohomology.PoitouTate.localFamily ι S v) σ)) =
    ((Langlands.GaloisCohomology.unitsModule (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)
              (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v))).ρ
          σ)
        ((Langlands.GaloisCohomology.PoitouTate.Internal.sInvLocalHom S ι ↑v) (Additive.ofMul t)) -
      (Langlands.GaloisCohomology.PoitouTate.Internal.sInvLocalHom S ι ↑v) (Additive.ofMul t)
Langlands.GaloisCohomology.PoitouTate.Internal.dataCond_unitsDatum.{u} {K : Type u} [Field K] [NumberField K]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (d : Langlands.GaloisCohomology.PoitouTate.Internal.UnitsDatum Ω S) :
  Langlands.GaloisCohomology.PoitouTate.Internal.DataCond (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
    (fun v =>
      Langlands.GaloisCohomology.unitsModule (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)))
    (fun v => Langlands.GaloisCohomology.PoitouTate.Internal.sUnitsLocalHom ι S ↑v)
    ((Langlands.GaloisCohomology.PoitouTate.Internal.sInvCochainHom Ω S) d)
    ((Langlands.GaloisCohomology.PoitouTate.Internal.dataLocalHom S ι) d)
Langlands.GaloisCohomology.PoitouTate.Internal.unitsData.{u} {K : Type u} [Field K] [NumberField K] {Ω : Type u}
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) :
  Langlands.GaloisCohomology.PoitouTate.Internal.UnitsDatum Ω S →+
    ↑(Langlands.GaloisCohomology.PoitouTate.Internal.unitsCompact ι S 1)
Langlands.GaloisCohomology.PoitouTate.Internal.unitsData_zero_left.{u} {K : Type u} [Field K] [NumberField K]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (a : (v : ↑S) → Additive (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)ˣ) :
  (Langlands.GaloisCohomology.PoitouTate.Internal.unitsData S ι) (0, a) =
    (ModuleCat.Hom.hom
        (Langlands.GaloisCohomology.localToCompact (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
          (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S)
          (fun v =>
            Langlands.GaloisCohomology.unitsModule (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)
              (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)))
          (fun v => Langlands.GaloisCohomology.PoitouTate.Internal.sUnitsLocalHom ι S ↑v) 0))
      fun v =>
      (ModuleCat.Hom.hom
          (Langlands.ProfiniteCohomology.zeroIso
              (Langlands.GaloisCohomology.unitsModule (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)
                (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)))).inv)
        ((Langlands.GaloisCohomology.unitsToInvariants (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)
            (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)))
          (a v))
Langlands.GaloisCohomology.PoitouTate.Internal.toMul_mem_sInvariantSubgroup.{u} {K : Type u} [Field K] [NumberField K]
  (Ω : Type u) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (T : Additive (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))ˣ)
  (x : ↑((Langlands.ProfiniteCohomology.cochains (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S)).X 1))
  (hT :
    ∀ (σ : Gal(↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)/K)),
      (Rep.Hom.hom (Langlands.GaloisCohomology.sUnitsToUnits S ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)))
          (Langlands.ProfiniteCohomology.cochainOf
            (Langlands.GaloisCohomology.sUnitsModule S ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) x ![σ]) =
        ((Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)).ρ σ) T -
          have this := T;
          this) :
  Additive.toMul T ∈ Langlands.GaloisCohomology.sInvariantSubgroup Ω S
Langlands.GaloisCohomology.PoitouTate.Internal.sInvCochain_eq_of.{u} {K : Type u} [Field K] [NumberField K] (Ω : Type u)
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (t : ↥(Langlands.GaloisCohomology.sInvariantSubgroup Ω S))
  (x : ↑((Langlands.ProfiniteCohomology.cochains (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S)).X 1))
  (hT :
    ∀ (σ : Gal(↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)/K)),
      (Rep.Hom.hom (Langlands.GaloisCohomology.sUnitsToUnits S ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)))
          (Langlands.ProfiniteCohomology.cochainOf
            (Langlands.GaloisCohomology.sUnitsModule S ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) x ![σ]) =
        ((Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)).ρ σ)
            (Additive.ofMul ↑t) -
          have this := Additive.ofMul ↑t;
          this) :
  Langlands.GaloisCohomology.PoitouTate.Internal.sInvCochain Ω S t = x
Langlands.GaloisCohomology.PoitouTate.Internal.isGalois_algebraicClosure_adicCompletion.{u} {K : Type u} [Field K]
  [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
  IsGalois (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
    (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
Langlands.GaloisCohomology.PoitouTate.Internal.exists_localUnitsHom_eq.{u} {K : Type u} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (y :
    ↑(Langlands.GaloisCohomology.unitsModule (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))))
  (hy :
    ∀
      (σ :
        Gal(AlgebraicClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion K
              v)/IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)),
      ((Langlands.GaloisCohomology.unitsModule (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
                (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))).ρ
            σ)
          y =
        y) :
  ∃ a, (Langlands.GaloisCohomology.PoitouTate.Internal.localUnitsHom v) a = y
Langlands.GaloisCohomology.PoitouTate.Internal.exists_unitsDatum.{u} {K : Type u} [Field K] [NumberField K] {Ω : Type u}
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (x : ↑((Langlands.ProfiniteCohomology.cochains (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S)).X 1))
  (y :
    (v : ↑S) →
      ↑(Langlands.GaloisCohomology.unitsModule (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v))))
  (hx :
    (ModuleCat.Hom.hom
          ((Langlands.ProfiniteCohomology.cochains (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S)).d 1 2))
        x =
      0)
  (hy :
    Langlands.GaloisCohomology.PoitouTate.Internal.DataCond (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
      (fun v =>
        Langlands.GaloisCohomology.unitsModule (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)))
      (fun v => Langlands.GaloisCohomology.PoitouTate.Internal.sUnitsLocalHom ι S ↑v) x y) :
  ∃ d,
    (Langlands.GaloisCohomology.PoitouTate.Internal.sInvCochainHom Ω S) d = x ∧
      (Langlands.GaloisCohomology.PoitouTate.Internal.dataLocalHom S ι) d = y
Langlands.GaloisCohomology.PoitouTate.Internal.unitsData_surjective.{u} {K : Type u} [Field K] [NumberField K]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) :
  Function.Surjective ⇑(Langlands.GaloisCohomology.PoitouTate.Internal.unitsData S ι)
Langlands.GaloisCohomology.PoitouTate.Internal.sInvOfUnit.{u} {K : Type u} [Field K] [NumberField K] (Ω : Type u)
  [Field Ω] [Algebra K Ω] (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (x : Kˣ) :
  ↥(Langlands.GaloisCohomology.sInvariantSubgroup Ω S)
Langlands.GaloisCohomology.PoitouTate.Internal.unitsModule_ρ_sInvOfUnit.{u} {K : Type u} [Field K] [NumberField K]
  (Ω : Type u) [Field Ω] [Algebra K Ω] (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (x : Kˣ) (σ : Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S) :
  ((Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)).ρ σ)
      (Additive.ofMul ↑(Langlands.GaloisCohomology.PoitouTate.Internal.sInvOfUnit Ω S x)) =
    Additive.ofMul ↑(Langlands.GaloisCohomology.PoitouTate.Internal.sInvOfUnit Ω S x)
Langlands.GaloisCohomology.PoitouTate.Internal.sInvLocalHom_sInvOfUnit.{u} {K : Type u} [Field K] [NumberField K]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (x : Kˣ) (v : ↑S) :
  (Langlands.GaloisCohomology.PoitouTate.Internal.sInvLocalHom S ι ↑v)
      (Additive.ofMul (Langlands.GaloisCohomology.PoitouTate.Internal.sInvOfUnit Ω S x)) =
    (Langlands.GaloisCohomology.PoitouTate.Internal.localUnitsHom ↑v)
      (Additive.ofMul ((Langlands.Global.finiteIdeleProjection K ↑v) ((Langlands.Global.diagonalUnits K) x)))
Langlands.GaloisCohomology.PoitouTate.Internal.unitsClass.{u} {K : Type u} [Field K] [NumberField K] (Ω : Type u)
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] :
  Langlands.GaloisCohomology.PoitouTate.Internal.UnitsDatum Ω S →+
    Additive (Langlands.GaloisCohomology.SIdeleClassGroup S)
Langlands.GaloisCohomology.PoitouTate.Internal.unitsClass_apply.{u} {K : Type u} [Field K] [NumberField K] (Ω : Type u)
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S]
  (d : Langlands.GaloisCohomology.PoitouTate.Internal.UnitsDatum Ω S) :
  (Langlands.GaloisCohomology.PoitouTate.Internal.unitsClass Ω S) d =
    Additive.ofMul
      ((Langlands.GaloisCohomology.sPresentation S)
        (fun w => Additive.toMul (d.2 w), Multiplicative.ofAdd (-(Langlands.GaloisCohomology.divAbove S) d.1)))
Langlands.GaloisCohomology.PoitouTate.Internal.mul_sInvOfUnit_mem_maximalSUnits.{u} {K : Type u} [Field K]
  [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (t : Additive ↥(Langlands.GaloisCohomology.sInvariantSubgroup Ω S)) (x : Kˣ)
  (h : (Langlands.GaloisCohomology.sDivisorOf S) (Additive.ofMul x) = -(Langlands.GaloisCohomology.divAbove S) t) :
  ↑(Additive.toMul (t + Additive.ofMul (Langlands.GaloisCohomology.PoitouTate.Internal.sInvOfUnit Ω S x))) ∈
    Langlands.GaloisCohomology.maximalSUnits K Ω S
Langlands.GaloisCohomology.PoitouTate.Internal.unitsData_eq_zero_of_unitsClass_eq_zero.{u} {K : Type u} [Field K]
  [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (d : Langlands.GaloisCohomology.PoitouTate.Internal.UnitsDatum Ω S)
  (h : (Langlands.GaloisCohomology.PoitouTate.Internal.unitsClass Ω S) d = 0) :
  (Langlands.GaloisCohomology.PoitouTate.Internal.unitsData S ι) d = 0
Langlands.GaloisCohomology.PoitouTate.Internal.unitsClass_surjective.{u} {K : Type u} [Field K] [NumberField K]
  (Ω : Type u) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite ↑S] :
  Function.Surjective ⇑(Langlands.GaloisCohomology.PoitouTate.Internal.unitsClass Ω S)
```

## Outline of the proofs

A datum of class zero is, by `ker_sPresentation`, of the form `(α a', ...)` with `α ∈ Kˣ` giving the
same local components and divisor; then `t α⁻¹` (`sInvOfUnit`) is an `S`-unit up to which `t` is
`α`, and the cocycle of the datum is the coboundary of the `0`-cochain `t α⁻¹ ∈ E` with the local
points, so its class is zero (`dataHom_eq_zero_of_boundary`, `mul_sInvOfUnit_mem_maximalSUnits`).
Surjectivity: a cycle `(x, y)` has `x` a `1`-cocycle in `E ⊆ K_Sˣ`, a coboundary `σ ↦ σ(t)/t` in
`K_Sˣ` by Hilbert 90 (`subsingleton_cohomology_one_unitsModule`); `t` is `S`-invariant
(`toMul_mem_sInvariantSubgroup`); the local points `y_v ι_v(t)⁻¹` are invariant, hence local units
`a_v ∈ K_vˣ` (`exists_localUnitsHom_eq`), and `(x, y)` is cohomologous to the cocycle of `(t, a)`
(`exists_dataCycle_eq`, `homologyπ_dataCycle_of_boundary`).

## Declarations

In the order of the file:

- `piConst` (def): A family of points of the local modules, as a family of constant `0`-cochains.
- `piConst_apply` (theorem).
- `piConst_add` (theorem).
- `DataCond` (def): The condition on `(x, y)` to be a `1`-cocycle with compact support: `x|_{H_v} = d y_v`.
- `dataCochain` (def): The cochain with compact support `(x, y)` in degree `1`.
- `dataCochain_add` (theorem).
- `localRes_one_eq_d_piConst` (theorem).
- `d_dataCochain` (theorem).
- `dataCycle` (def): The cocycle with compact support `(x, y)`.
- `iCycles_dataCycle` (theorem).
- `dataCycle_congr` (theorem).
- `dataCond_add` (theorem).
- `dataCond_zero` (theorem).
- `dataHom` (def): A homomorphism from a group of data to `H_c¹`.
- `dataHom_apply` (theorem).
- `exists_dataCycle_eq` (theorem): Every `1`-cocycle with compact support is a `dataCycle`.
- `dataHom_surjective` (theorem): `dataHom` is surjective when every pair `(x, y)` with the cocycle condition comes from a datum.
- `homologyπ_dataCycle_of_boundary` (theorem): The class of `(d α, (a_v α)_v)` is zero.
- `dataHom_eq_zero_of_boundary` (theorem).
- `exists_coboundary_of_subsingleton` (theorem): A `1`-cocycle of `U` whose image in `X` has `H¹(X) = 0` is the coboundary of a point of `X`.
- `homologyπ_dataCycle_zero_of_invariant` (theorem): A datum with zero global part and invariant local points is the image of the local classes of degree `0`.
- `dataHom_eq_localToCompact` (theorem).
- `sInvRatio` (def): `σ(t)/t ∈ 𝒪_Sˣ` for an `S`-invariant unit `t`.
- `sUnitsToUnits_sInvRatio` (theorem): The image of `σ(t)/t` in `K_Sˣ` is `σ · t - t` (additively).
- `sInvRatio_mul` (theorem).
- `isLocallyConstant_sInvRatio` (theorem).
- `sInvCochain` (def): The `1`-cocycle `σ ↦ σ(t)/t` of `G_S` in `𝒪_Sˣ`.
- `cochainOf_sInvCochain` (theorem).
- `sInvCochain_mul` (theorem).
- `sInvCochain_one` (theorem).
- `cochainsMap_sUnitsToUnits_sInvCochain` (theorem): In `K_Sˣ`, the cocycle `σ ↦ σ(t)/t` is the coboundary of `t`.
- `d_sInvCochain` (theorem).
- `localUnitsHom` (def): The units of `K_v` in `K̄_vˣ`.
- `sInvLocalHom` (def): An `S`-invariant unit of `K_S` in `K̄_vˣ` (by `ι`).
- `localUnitsHom_invariant` (theorem).
- `UnitsDatum` (abbrev): The data of degree `1` with compact support: an `S`-invariant unit `t` of `K_S` and local units `a_v ∈ K_vˣ` at the places of `S`.
- `dataLocalHom` (def): The local component `a_v + ι_v(t)` (additive notation) of the datum `(t, a)`.
- `dataLocalHom_apply` (theorem).
- `sInvCochainHom` (def): The global component `σ ↦ σ(t)/t` of the datum `(t, a)`.
- `sUnitsLocalHom_sInvRatio` (theorem).
- `dataCond_unitsDatum` (theorem).
- `unitsData` (def): **The classes of the data.**
- `unitsData_zero_left` (theorem): On data `(1, a)`, `unitsData` is `localToCompact` of the local units.
- `toMul_mem_sInvariantSubgroup` (theorem): An `S`-invariant unit from a coboundary in `K_Sˣ` of a cocycle with values in `𝒪_Sˣ`.
- `sInvCochain_eq_of` (theorem).
- `isGalois_algebraicClosure_adicCompletion` (instance).
- `exists_localUnitsHom_eq` (theorem): An invariant point of `K̄_vˣ` comes from `K_vˣ`.
- `exists_unitsDatum` (theorem).
- `unitsData_surjective` (theorem): **Every class of `H_c¹(G_S, 𝒪_Sˣ)` comes from a datum** (Hilbert 90 for `K_Sˣ`).
- `sInvOfUnit` (def): A unit of `K` as an `S`-invariant unit of `K_S`.
- `unitsModule_ρ_sInvOfUnit` (theorem).
- `sInvLocalHom_sInvOfUnit` (theorem).
- `unitsClass` (def): **The `S`-idèle class of a datum** `(t, a)`: `sPresentation ((a_v)_v, -div(t))`.
- `unitsClass_apply` (theorem).
- `mul_sInvOfUnit_mem_maximalSUnits` (theorem).
- `unitsData_eq_zero_of_unitsClass_eq_zero` (theorem): `unitsData` vanishes on the data of `S`-idèle class zero.
- `unitsClass_surjective` (theorem): **Every `S`-idèle class is the class of a datum**: by the presentation of the `S`-idèle class group and the principal ideal theorem (`divAbove_surjective`).

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseClass.lean` and `src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseClassIdele.lean`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's mapping cocone (`mappingCoconeNat`), cochains (`cochains`, `cochainOf`), `localRes`, `sPresentation`, `divAbove` and `unitsModule` replace the source's cone, `cochainsComplex`, `gsLocalRes`, its presentation of the `S`-idèle class group and `galUnits`; the data are additive (`Additive`), and `dataHom` is stated for an arbitrary family of local groups.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition, corrected printing (Springer, 2013), Chapter VIII, §3, Proposition (8.3.11), p. 458 (`H¹(G_S, 𝒪_Sˣ)` is the `S`-class group);
  Chapter VIII, §6, p. 482 (the exact sequence `0 → 𝒪_Sˣ → I_S → C_S → 0`, through which the
  `S`-idèle classes give the classes of `H_c¹` of the `S`-units).
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge, 2006), Chapter II, §2, Remark 2.2, p. 165.
