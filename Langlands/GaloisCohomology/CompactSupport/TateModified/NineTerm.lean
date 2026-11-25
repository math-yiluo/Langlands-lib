import Langlands.GaloisCohomology.CompactSupport.NineTerm
import Langlands.GaloisCohomology.CompactSupport.TateModified.Duality
import Langlands.GaloisCohomology.CompactSupport.TateModified.OpenSubgroup
import Langlands.Cohomology.Profinite.InflationRestriction.DegreeOne

/-!
# The nine-term sequence of Poitou–Tate with Tate's `Ĥ⁰` (abstract form)

The version of `NineTerm.lean` with a second family of finite groups `F_w`, at which degree `0` is
Tate's `Ĥ⁰`: under `TatePoitouTateHypotheses` the sequence
`0 → H⁰(M) → P̂⁰ → H²(M')^∨ → H¹(M) → P¹ → H¹(M')^∨ → H²(M) → P² → H⁰(M')^∨ → 0`, with
`P̂⁰ = ∏_v H⁰(H_v, M) × ∏_w Ĥ⁰(F_w, M)` and `Pʳ = ∏_v Hʳ(H_v, M) × ∏_w Hʳ(F_w, M)`, is exact
(`IsTateNineTermExact`, `TatePoitouTateHypotheses.isTateNineTermExact`), and `Ш¹(M)`, `Ш²(M')`
are finite and in perfect duality. As in `NineTerm.lean`, the connecting maps take no proof as
argument.
-/

namespace Langlands.GaloisCohomology

open Langlands Langlands.ProfiniteCohomology

universe u

-- from PoitouTate/RealDefs.lean
section RealDefs

noncomputable section


open CategoryTheory MonoidalCategory

attribute [local instance 2000] Rep.hV2

section NormClass

variable {k F : Type u} [CommRing k] [Group F] [TopologicalSpace F] [IsTopologicalGroup F] [Fintype F]

theorem exists_normClass_cycle (B : Rep k F) [IsSmoothRep B] (m : B) :
    ∃ z : (cochains B).cycles 0, normClass B m = ((cochains B).homologyπ 0).hom z ∧
      ((cochains B).iCycles 0).hom z = zeroCochain B (B.ρ.norm m) :=
  ⟨_, rfl, (cochains B).i_cyclesMk _ _ _ _⟩

theorem H0Iso_hom_normClass (B : Rep k F) [IsSmoothRep B] (m : B) :
    (((zeroIso B).hom.hom (normClass B m) : B.ρ.invariants) : B) = B.ρ.norm m := by
  obtain ⟨z, hz, hiz⟩ := exists_normClass_cycle B m
  rw [hz]
  refine (zeroIso_hom_cohomology_class_zero B z).trans ?_
  change cochainOf B (((cochains B).iCycles 0).hom z) Fin.elim0 = _
  rw [hiz]
  rfl

theorem normClass_mem_normClasses (B : Rep k F) [IsSmoothRep B] (m : B) :
    normClass B m ∈ normClasses B := by
  have hN : B.ρ.norm m ∈ B.ρ.invariants := fun g => Representation.self_norm_apply _ _ _
  refine (mem_normClasses_iff B _).2 ⟨m, hN, ?_⟩
  have key : (zeroIso B).hom.hom (normClass B m) = ⟨B.ρ.norm m, hN⟩ :=
    Subtype.ext (H0Iso_hom_normClass B m)
  rw [← key]
  exact (hom_apply_hom_apply_of_comp_eq (zeroIso B).hom_inv_id _).symm

theorem exists_normClass_eq_of_mem (B : Rep k F) [IsSmoothRep B] (x : cohomology B 0)
    (hx : x ∈ normClasses B) : ∃ m, normClass B m = x := by
  obtain ⟨a, h, rfl⟩ := (mem_normClasses_iff B x).1 hx
  refine ⟨a, ?_⟩
  have key : (zeroIso B).hom.hom (normClass B a) = ⟨B.ρ.norm a, h⟩ :=
    Subtype.ext (H0Iso_hom_normClass B a)
  rw [← key]
  exact (hom_apply_hom_apply_of_comp_eq (zeroIso B).hom_inv_id _).symm

theorem cupPairing_normClass_eq_zero {X Y Z : Rep k F} [IsSmoothRep X] [IsSmoothRep Y]
    [IsSmoothRep Z] (μ : X ⊗ Y ⟶ Z) (e : X) {s : ℕ} (y : cohomology Y (s + 1)) :
    cupPairing μ (zero_add (s + 1)) (normClass X e) y = 0 := by
  rw [← cupLeibniz_homology]
  obtain ⟨c, rfl⟩ := homologyπ_hom_surjective _ (s + 1) y
  obtain ⟨z, hz, hiz⟩ := exists_normClass_cycle X e
  rw [hz, LeibnizPairing.homology_homologyπ]
  refine (homologyπ_succ_eq_zero_iff (cochains Z) s _).2
    ⟨normHomotopy μ rfl e (((cochains Y).iCycles (s + 1)).hom c), ?_⟩
  rw [LeibnizPairing.iCycles_cycles]
  have hd : ((cochains Y).d (s + 1) (s + 1 + 1)).hom
      (((cochains Y).iCycles (s + 1)).hom c) = 0 :=
    (hom_apply_hom_apply_of_comp_eq ((cochains Y).iCycles_d (s + 1) (s + 1 + 1)) c).trans rfl
  have key := d_normHomotopy_add μ e (((cochains Y).iCycles (s + 1)).hom c)
  rw [hd, map_zero, add_zero] at key
  rw [key, hiz]
  rfl

end NormClass

section Sequence

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  (M : Rep (ULift.{u} ℤ) G) [IsSmoothRep M]

/-- The local terms `∏_v Hʳ(H_v, M) × ∏_w Hʳ(F_w, M)` of the Tate-modified nine-term sequence. -/
abbrev ptTLocal (r : ℕ) : Type u :=
  (∀ v, cohomology (Rep.res (φ v : Hv v →* G) M) r) × (∀ w, cohomology (Rep.res (ψ w : F w →* G) M) r)

/-- Localization to all local groups. -/
abbrev ptTGlobalToLocal (r : ℕ) :=
  tateGlobalToLocal φ ψ M (fun v => Rep.res (φ v : Hv v →* G) M) (fun _ => 𝟙 _)
    (fun w => Rep.res (ψ w : F w →* G) M) (fun _ => 𝟙 _) r

/-- The map `Ĥ_c^r(G, M) → Hʳ(G, M)`. -/
abbrev ptTToGlobal (r : ℕ) :=
  tateToGlobal φ ψ M (fun v => Rep.res (φ v : Hv v →* G) M) (fun _ => 𝟙 _)
    (fun w => Rep.res (ψ w : F w →* G) M) (fun _ => 𝟙 _) r

/-- The map from the local terms to `Ĥ_c^{r+1}(G, M)`. -/
abbrev ptTLocalToCompact (r : ℕ) :=
  tateLocalToCompact φ ψ M (fun v => Rep.res (φ v : Hv v →* G) M) (fun _ => 𝟙 _)
    (fun w => Rep.res (ψ w : F w →* G) M) (fun _ => 𝟙 _) r

omit [∀ w, Fintype (F w)] in
theorem ptTGlobalToLocal_apply (r : ℕ) (x : cohomology M r) :
    (ptTGlobalToLocal φ ψ M r).hom x = (fun v => ptRes φ M v r x, fun w => ptRes ψ M w r x) :=
  tateGlobalToLocal_hom_apply φ ψ M _ _ _ _ r x

theorem ptTExact_global (r : ℕ) :
    Function.Exact (ptTToGlobal φ ψ M (r + 1)).hom (ptTGlobalToLocal φ ψ M (r + 1)).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (tateCompactCohomology_exact_global φ ψ M _ (fun _ => 𝟙 _) _ (fun _ => 𝟙 _) r)

theorem ptTExact_local (r : ℕ) :
    Function.Exact (ptTGlobalToLocal φ ψ M (r + 1)).hom (ptTLocalToCompact φ ψ M (r + 1)).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (tateCompactCohomology_exact_local φ ψ M _ (fun _ => 𝟙 _) _ (fun _ => 𝟙 _) r)

theorem ptTExact_compact (r : ℕ) :
    Function.Exact (ptTLocalToCompact φ ψ M r).hom (ptTToGlobal φ ψ M (r + 1)).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (tateCompactCohomology_exact_compact φ ψ M _ (fun _ => 𝟙 _) _ (fun _ => 𝟙 _) r)

/-- The local terms in degree `0` with Tate's `Ĥ⁰` at the finite groups. -/
abbrev ptTLocalHat : Type u :=
  (∀ v, cohomology (Rep.res (φ v : Hv v →* G) M) 0) ×
    (∀ w, cohomologyTateZero (Rep.res (ψ w : F w →* G) M))

/-- The quotient map from `H⁰` to `Ĥ⁰` at the finite groups. -/
def ptTHatMk : ptTLocal φ ψ M 0 →+ ptTLocalHat φ ψ M :=
  AddMonoidHom.prodMap (AddMonoidHom.id _)
    (AddMonoidHom.pi fun w => (normClasses (Rep.res (ψ w : F w →* G) M)).mkQ.toAddMonoidHom.comp
      (Pi.evalAddMonoidHom (fun w => cohomology (Rep.res (ψ w : F w →* G) M) 0) w))

omit [IsTopologicalGroup G] in
theorem ptTHatMk_apply (ξ : ptTLocal φ ψ M 0) :
    ptTHatMk φ ψ M ξ = (ξ.1, fun w => Submodule.Quotient.mk (ξ.2 w)) :=
  rfl

omit [IsTopologicalGroup G] in
theorem ptTHatMk_surjective : Function.Surjective (ptTHatMk φ ψ M) := fun ξ => by
  choose y hy using fun w => Submodule.Quotient.mk_surjective _ (ξ.2 w)
  exact ⟨(ξ.1, y), Prod.ext rfl (funext hy)⟩

omit [IsTopologicalGroup G] in
theorem ptTHatMk_eq_zero_iff (ξ : ptTLocal φ ψ M 0) :
    ptTHatMk φ ψ M ξ = 0 ↔ ξ.1 = 0 ∧ ∀ w, ξ.2 w ∈ normClasses (Rep.res (ψ w : F w →* G) M) := by
  rw [ptTHatMk_apply]
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, fun w =>
      (Submodule.Quotient.mk_eq_zero _).1 (congrFun (congrArg Prod.snd h) w)⟩
  · rintro ⟨h1, h2⟩
    exact Prod.ext h1 (funext fun w => (Submodule.Quotient.mk_eq_zero _).2 (h2 w))

/-- Localization in degree `0`, with `Ĥ⁰` at the finite groups. -/
def ptTGlobalToLocalHat : cohomology M 0 →+ ptTLocalHat φ ψ M :=
  (ptTHatMk φ ψ M).comp (ptTGlobalToLocal φ ψ M 0).hom.toAddMonoidHom

theorem ptTGlobalToLocalHat_apply (x : cohomology M 0) :
    ptTGlobalToLocalHat φ ψ M x = ptTHatMk φ ψ M ((ptTGlobalToLocal φ ψ M 0).hom x) :=
  rfl

/-- An additive map descends along a surjection whose kernel it kills. -/
def descendAddHom {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (f : A →+ B)
    (hf : Function.Surjective f) (g : A →+ C) (h : f.ker ≤ g.ker) : B →+ C :=
  (QuotientAddGroup.lift _ g h).comp
    (QuotientAddGroup.quotientKerEquivOfSurjective f hf).symm.toAddMonoidHom

theorem descendAddHom_apply {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A →+ B) (hf : Function.Surjective f) (g : A →+ C) (h : f.ker ≤ g.ker) (a : A) :
    descendAddHom f hf g h (f a) = g a := by
  have e : (QuotientAddGroup.quotientKerEquivOfSurjective f hf).symm (f a) = (a : A ⧸ f.ker) :=
    (AddEquiv.symm_apply_eq _).2 rfl
  change QuotientAddGroup.lift _ g h ((QuotientAddGroup.quotientKerEquivOfSurjective f hf).symm (f a)) = g a
  rw [e]
  rfl

theorem ptTLocalToCompact_of_hatMk_eq_zero (ξ : ptTLocal φ ψ M 0) (hξ : ptTHatMk φ ψ M ξ = 0) :
    (ptTLocalToCompact φ ψ M 0).hom ξ = 0 := by
  obtain ⟨h1, h2⟩ := (ptTHatMk_eq_zero_iff φ ψ M ξ).1 hξ
  choose e he using fun w => exists_normClass_eq_of_mem _ (ξ.2 w) (h2 w)
  have hx : (tateGlobalZeroToLocal φ ψ M (fun v => Rep.res (φ v : Hv v →* G) M) (fun _ => 𝟙 _)
      (fun w => Rep.res (ψ w : F w →* G) M) (fun _ => 𝟙 _)).hom (0, e) = ξ := by
    rw [tateGlobalZeroToLocal_hom_apply, map_zero, map_zero, zero_add]
    exact Prod.ext h1.symm (funext he)
  rw [← hx]
  exact hom_apply_hom_apply_of_comp_eq (tateGlobalZeroToLocal_tateLocalToCompact φ ψ M _ _ _ _) _

/-- The map from the degree-`0` local terms (with `Ĥ⁰`) to `Ĥ_c^1(G, M)`. -/
def ptTLocalHatToCompact : ptTLocalHat φ ψ M →+ tateCompactCohomologyRes φ ψ M 1 :=
  descendAddHom (ptTHatMk φ ψ M) (ptTHatMk_surjective φ ψ M)
    (ptTLocalToCompact φ ψ M 0).hom.toAddMonoidHom
    fun ξ hξ => ptTLocalToCompact_of_hatMk_eq_zero φ ψ M ξ hξ

theorem ptTLocalHatToCompact_hatMk (ξ : ptTLocal φ ψ M 0) :
    ptTLocalHatToCompact φ ψ M (ptTHatMk φ ψ M ξ) = (ptTLocalToCompact φ ψ M 0).hom ξ :=
  descendAddHom_apply _ _ _ _ ξ

/-- `Шʳ(M)` for the localization to all local groups. -/
def ptTSha (r : ℕ) : AddSubgroup (cohomology M r) :=
  (ptTGlobalToLocal φ ψ M r).hom.toAddMonoidHom.ker

omit [∀ w, Fintype (F w)] in
theorem mem_ptTSha {r : ℕ} (x : cohomology M r) :
    x ∈ ptTSha φ ψ M r ↔ (ptTGlobalToLocal φ ψ M r).hom x = 0 :=
  AddMonoidHom.mem_ker

theorem ptTToGlobal_mem_ptTSha {r : ℕ} (x : tateCompactCohomologyRes φ ψ M (r + 1)) :
    (ptTToGlobal φ ψ M (r + 1)).hom x ∈ ptTSha φ ψ M (r + 1) :=
  (mem_ptTSha φ ψ M _).2 ((ptTExact_global φ ψ M r _).2 ⟨x, rfl⟩)

theorem exists_ptTToGlobal_eq_of_mem_ptTSha {r : ℕ} {x : cohomology M (r + 1)}
    (hx : x ∈ ptTSha φ ψ M (r + 1)) :
    ∃ y : tateCompactCohomologyRes φ ψ M (r + 1), (ptTToGlobal φ ψ M (r + 1)).hom y = x :=
  (ptTExact_global φ ψ M r x).1 ((mem_ptTSha φ ψ M x).1 hx)

end Sequence

section Pairings

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G) [Fintype ι]
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G) [Fintype κ]
  (D : Rep (ULift.{u} ℤ) G) [IsSmoothRep D]
  (M : Rep (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M]
  (inv : ∀ v, cohomology (Rep.res (φ v : Hv v →* G) D) 2 →+ QZ)
  (invr : ∀ w, cohomology (Rep.res (ψ w : F w →* G) D) 2 →+ QZ)

/-- The sum of the local pairings at both families, as a map to the dual of global cohomology. -/
def ptTLocalDualMap {r s : ℕ} (h : r + s = 2) :
    ptTLocal φ ψ M r →+ (cohomology (dualRep D M) s →+ QZ) :=
  (ptLocalDualMap φ D M inv h).comp (AddMonoidHom.fst _ _) +
    (ptLocalDualMap ψ D M invr h).comp (AddMonoidHom.snd _ _)

omit [∀ w, Fintype (F w)] in
theorem ptTLocalDualMap_apply {r s : ℕ} (h : r + s = 2) (ξ : ptTLocal φ ψ M r)
    (y : cohomology (dualRep D M) s) :
    ptTLocalDualMap φ ψ D M inv invr h ξ y =
      ∑ v, ptLocalPairing φ D M inv v h (ξ.1 v) (ptRes φ (dualRep D M) v s y) +
        ∑ w, ptLocalPairing ψ D M invr w h (ξ.2 w) (ptRes ψ (dualRep D M) w s y) := by
  change ptLocalDualMap φ D M inv h ξ.1 y + ptLocalDualMap ψ D M invr h ξ.2 y = _
  rw [ptLocalDualMap_apply, ptLocalDualMap_apply]

theorem ptTLocalDualMap_of_hatMk_eq_zero (ξ : ptTLocal φ ψ M 0) (hξ : ptTHatMk φ ψ M ξ = 0) :
    ptTLocalDualMap φ ψ D M inv invr (show 0 + 2 = 2 from rfl) ξ = 0 := by
  obtain ⟨h1, h2⟩ := (ptTHatMk_eq_zero_iff φ ψ M ξ).1 hξ
  refine AddMonoidHom.ext fun y => ?_
  rw [ptTLocalDualMap_apply, AddMonoidHom.zero_apply, h1]
  refine (congrArg₂ (· + ·) (Finset.sum_eq_zero fun v _ => ?_) (Finset.sum_eq_zero fun w _ => ?_)).trans
    (add_zero 0)
  · exact DFunLike.congr_fun (map_zero (ptLocalPairing φ D M inv v (show 0 + 2 = 2 from rfl))) _
  · obtain ⟨e, he⟩ := exists_normClass_eq_of_mem _ (ξ.2 w) (h2 w)
    rw [ptLocalPairing_apply, ← he]
    refine (congrArg (invr w) ?_).trans (map_zero _)
    exact cupPairing_normClass_eq_zero (s := 1) _ e _

/-- The sum of the local pairings in degree `0`, through `Ĥ⁰` at the finite groups. -/
def ptTLocalHatDualMap : ptTLocalHat φ ψ M →+ (cohomology (dualRep D M) 2 →+ QZ) :=
  descendAddHom (ptTHatMk φ ψ M) (ptTHatMk_surjective φ ψ M)
    (ptTLocalDualMap φ ψ D M inv invr (show 0 + 2 = 2 from rfl))
    fun ξ hξ => ptTLocalDualMap_of_hatMk_eq_zero φ ψ D M inv invr ξ hξ

theorem ptTLocalHatDualMap_hatMk (ξ : ptTLocal φ ψ M 0) :
    ptTLocalHatDualMap φ ψ D M inv invr (ptTHatMk φ ψ M ξ) =
      ptTLocalDualMap φ ψ D M inv invr (show 0 + 2 = 2 from rfl) ξ :=
  descendAddHom_apply _ _ _ _ ξ

variable {n : ℕ} (t : tateCompactCohomologyRes φ ψ D 3 →+ ZMod n)

/-- The Tate-modified duality map `Ĥ_c^r(G, M) → Hˢ(G, M')^∨`. -/
def ptTCompactDualMap {r s : ℕ} (h : r + s = 3) :
    tateCompactCohomologyRes φ ψ M r →+ (cohomology (dualRep D M) s →+ QZ) :=
  (AddMonoidHom.compHom ((zmodToQZ n).comp t)).comp
    (bilinAddHom (tateCompactCupRes φ ψ (evalPairing D M) h))

omit [Fintype ι] [Fintype κ] in
theorem ptTCompactDualMap_apply {r s : ℕ} (h : r + s = 3) (x : tateCompactCohomologyRes φ ψ M r)
    (y : cohomology (dualRep D M) s) :
    ptTCompactDualMap φ ψ D M t h x y =
      zmodToQZ n (t (tateCompactCupRes φ ψ (evalPairing D M) h x y)) :=
  rfl

omit [Fintype ι] [Fintype κ] in

theorem tateCompactCupRes_ptTLocalToCompact {r s : ℕ} (h : r + s = 2) (h' : r + 1 + s = 3)
    (ξ : ptTLocal φ ψ M r) (y : cohomology (dualRep D M) s) :
    tateCompactCupRes φ ψ (evalPairing D M) h' ((ptTLocalToCompact φ ψ M r).hom ξ) y =
      (ptTLocalToCompact φ ψ D 2).hom
        (fun v => cupPairing (ptLocalEval φ D M v) h (ξ.1 v) (ptRes φ (dualRep D M) v s y),
          fun w => cupPairing (ptLocalEval ψ D M w) h (ξ.2 w) (ptRes ψ (dualRep D M) w s y)) :=
  tateCompactCup_tateLocalToCompact φ ψ (evalPairing D M) _ _ _ _ h h' ξ y

omit [Fintype ι] [Fintype κ] [∀ w, Fintype (F w)] [Finite M] in
theorem ptRes_eq_zero_of_mem_ptTSha {r : ℕ} {x : cohomology M r} (hx : x ∈ ptTSha φ ψ M r) :
    (∀ v, ptRes φ M v r x = 0) ∧ ∀ w, ptRes ψ M w r x = 0 := by
  have h := (mem_ptTSha φ ψ M x).1 hx
  rw [ptTGlobalToLocal_apply] at h
  exact ⟨fun v => congrFun (congrArg Prod.fst h) v, fun w => congrFun (congrArg Prod.snd h) w⟩

omit [Fintype ι] [Fintype κ] in

theorem ptTCompactDualMap_eq_zero_of_ptTToGlobal_eq_zero {x : tateCompactCohomologyRes φ ψ M 1}
    (hx : (ptTToGlobal φ ψ M 1).hom x = 0) {y : cohomology (dualRep D M) 2}
    (hy : y ∈ ptTSha φ ψ (dualRep D M) 2) :
    ptTCompactDualMap φ ψ D M t (show 1 + 2 = 3 from rfl) x y = 0 := by
  obtain ⟨ξ, rfl⟩ := (ptTExact_compact φ ψ M 0 x).1 hx
  obtain ⟨h1, h2⟩ := ptRes_eq_zero_of_mem_ptTSha φ ψ (dualRep D M) hy
  rw [ptTCompactDualMap_apply, tateCompactCupRes_ptTLocalToCompact φ ψ D M (show 0 + 2 = 2 from rfl)]
  have h0 : ((fun v => cupPairing (ptLocalEval φ D M v) (show 0 + 2 = 2 from rfl) (ξ.1 v)
      (ptRes φ (dualRep D M) v 2 y)), (fun w => cupPairing (ptLocalEval ψ D M w)
        (show 0 + 2 = 2 from rfl) (ξ.2 w) (ptRes ψ (dualRep D M) w 2 y))) = (0 : ptTLocal φ ψ D 2) := by
    refine Prod.ext (funext fun v => ?_) (funext fun w => ?_)
    · change cupPairing (ptLocalEval φ D M v) (show 0 + 2 = 2 from rfl) (ξ.1 v)
        (ptRes φ (dualRep D M) v 2 y) = 0
      rw [h1 v]
      exact map_zero _
    · change cupPairing (ptLocalEval ψ D M w) (show 0 + 2 = 2 from rfl) (ξ.2 w)
        (ptRes ψ (dualRep D M) w 2 y) = 0
      rw [h2 w]
      exact map_zero _
  rw [h0, map_zero, map_zero, map_zero]

/-- A lift of an element of `Ш¹(M)` to `Ĥ_c^1(G, M)` (a choice). -/
def ptTShaLift (x : ptTSha φ ψ M 1) : tateCompactCohomologyRes φ ψ M 1 :=
  (exists_ptTToGlobal_eq_of_mem_ptTSha φ ψ M (r := 0) x.2).choose

omit [Fintype ι] [Fintype κ] [Finite M] in
theorem ptTToGlobal_ptTShaLift (x : ptTSha φ ψ M 1) :
    (ptTToGlobal φ ψ M 1).hom (ptTShaLift φ ψ M x) = x :=
  (exists_ptTToGlobal_eq_of_mem_ptTSha φ ψ M (r := 0) x.2).choose_spec

/-- The pairing `Ш¹(M) × Ш²(M') → ℚ/ℤ` (Tate-modified version). -/
def ptTShaPairing : ptTSha φ ψ M 1 →+ ptTSha φ ψ (dualRep D M) 2 →+ QZ where
  toFun x := (ptTCompactDualMap φ ψ D M t (show 1 + 2 = 3 from rfl) (ptTShaLift φ ψ M x)).comp
    (ptTSha φ ψ (dualRep D M) 2).subtype
  map_zero' := by
    refine AddMonoidHom.ext fun y => ?_
    refine ptTCompactDualMap_eq_zero_of_ptTToGlobal_eq_zero φ ψ D M t ?_ y.2
    rw [ptTToGlobal_ptTShaLift]
    rfl
  map_add' x x' := by
    refine AddMonoidHom.ext fun y => ?_
    have hz := ptTCompactDualMap_eq_zero_of_ptTToGlobal_eq_zero φ ψ D M t
      (x := ptTShaLift φ ψ M (x + x') - ptTShaLift φ ψ M x - ptTShaLift φ ψ M x') ?_ y.2
    · rw [map_sub, map_sub, AddMonoidHom.sub_apply, AddMonoidHom.sub_apply, sub_sub,
        sub_eq_zero] at hz
      simpa using hz
    · rw [map_sub, map_sub, ptTToGlobal_ptTShaLift, ptTToGlobal_ptTShaLift, ptTToGlobal_ptTShaLift]
      simp

omit [Fintype ι] [Fintype κ] in

theorem ptTShaPairing_apply (x : tateCompactCohomologyRes φ ψ M 1) (y : ptTSha φ ψ (dualRep D M) 2) :
    ptTShaPairing φ ψ D M t ⟨_, ptTToGlobal_mem_ptTSha φ ψ M (r := 0) x⟩ y =
      ptTCompactDualMap φ ψ D M t (show 1 + 2 = 3 from rfl) x y := by
  have hz := ptTCompactDualMap_eq_zero_of_ptTToGlobal_eq_zero φ ψ D M t
    (x := ptTShaLift φ ψ M ⟨_, ptTToGlobal_mem_ptTSha φ ψ M (r := 0) x⟩ - x) ?_ y.2
  · rw [map_sub, AddMonoidHom.sub_apply, sub_eq_zero] at hz
    exact hz
  · rw [map_sub, ptTToGlobal_ptTShaLift, sub_self]

end Pairings

end

end RealDefs

-- from PoitouTate/RealAbstract.lean
section RealAbstract

noncomputable section


open CategoryTheory MonoidalCategory

attribute [local instance 2000] Rep.hV2

theorem finite_of_finite_addMonoidHom_zmod {A : Type*} [AddCommGroup A] {n : ℕ} [NeZero n]
    (hA : ∀ a : A, n • a = 0) [Finite (A →+ ZMod n)] : Finite A := by
  refine Finite.of_injective (fun a (χ : A →+ ZMod n) => χ a) fun a b hab => ?_
  by_contra hne
  obtain ⟨χ, hχ⟩ := QZ.exists_apply_ne_zero (sub_ne_zero.2 hne)
  have hn : ∀ x, n • χ x = 0 := fun x => by rw [← map_nsmul, hA, map_zero]
  have h := congrFun hab (zmodOfQZ χ hn)
  apply hχ
  rw [map_sub, ← zmodToQZ_zmodOfQZ χ hn a, ← zmodToQZ_zmodOfQZ χ hn b]
  change zmodToQZ n (zmodOfQZ χ hn a) - zmodToQZ n (zmodOfQZ χ hn b) = 0
  rw [show zmodOfQZ χ hn a = zmodOfQZ χ hn b from h, sub_self]

section NormZero

variable {k F : Type u} [CommRing k] [Group F] [TopologicalSpace F] [IsTopologicalGroup F] [Fintype F]

theorem normClass_zero (B : Rep k F) [IsSmoothRep B] : normClass B 0 = 0 := by
  have h : (zeroIso B).hom.hom (normClass B 0) = 0 :=
    Subtype.ext ((H0Iso_hom_normClass B 0).trans (map_zero _))
  calc normClass B 0 = (zeroIso B).inv.hom ((zeroIso B).hom.hom (normClass B 0)) :=
        (hom_apply_hom_apply_of_comp_eq (zeroIso B).hom_inv_id _).symm
    _ = 0 := by rw [h, map_zero]

end NormZero

section Hypotheses

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G) [Fintype ι]
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G) [Fintype κ]
  {n : ℕ} [NeZero n] (D : Rep (ULift.{u} ℤ) G) [IsSmoothRep D]
  (t : tateCompactCohomologyRes φ ψ D 3 →+ ZMod n)
  (inv : ∀ v, cohomology (Rep.res (φ v : Hv v →* G) D) 2 →+ QZ)
  (invr : ∀ w, cohomology (Rep.res (ψ w : F w →* G) D) 2 →+ QZ)

/-- The hypotheses of the Tate-modified nine-term sequence. -/
structure TatePoitouTateHypotheses : Prop where
  /-- The dualizing module is cyclic of order `n`. -/
  nonempty_addEquiv : Nonempty (D ≃+ ZMod n)
  /-- Tate-modified duality `Hʳ(G, M') ≅ Ĥ_c^s(G, M)^∨` for `r + s = 3`, `s ≥ 1`, and finite `M` killed by `n`. -/
  duality : ∀ (M : Rep (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M], (∀ m : M, n • m = 0) →
    ∀ {r s : ℕ} (h : r + s = 3), 1 ≤ s → Function.Bijective (tateCompactDualityMap φ ψ D h t M)
  /-- `Hʳ(G, M)` is finite for `r ≤ 2` and finite `M` killed by `n`. -/
  finite_cohomology : ∀ (M : Rep (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M],
    (∀ m : M, n • m = 0) → ∀ r, r ≤ 2 → Finite (cohomology M r)
  /-- The trace restricts on the local terms in degree 2 to the sum of the local invariants (at both families). -/
  localToCompact_two : ∀ ξ : ptTLocal φ ψ D 2,
    zmodToQZ n (t ((ptTLocalToCompact φ ψ D 2).hom ξ)) = ∑ v, inv v (ξ.1 v) + ∑ w, invr w (ξ.2 w)
  /-- `H⁰(G, M) → ∏_v H⁰(H_v, M)` is injective. -/
  injective_res_zero : ∀ (M : Rep (ULift.{u} ℤ) G) [IsSmoothRep M],
    Function.Injective fun (x : cohomology M 0) v => ptRes φ M v 0 x
  /-- The local pairings at the first family in degrees `(0, 2)` are surjective. -/
  surjective_localPairing_zero : ∀ (M : Rep (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M],
    (∀ m : M, n • m = 0) → ∀ v,
      Function.Surjective (ptLocalPairing φ D M inv v (show 0 + 2 = 2 from rfl))
  /-- The local pairings at the first family in degrees `(2, 0)` are surjective. -/
  surjective_localPairing_two : ∀ (M : Rep (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M],
    (∀ m : M, n • m = 0) → ∀ v,
      Function.Surjective (ptLocalPairing φ D M inv v (show 2 + 0 = 2 from rfl))
  /-- The local pairings at the finite groups in degrees `(0, 2)` are surjective. -/
  surjective_realPairing_zero : ∀ (M : Rep (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M],
    (∀ m : M, n • m = 0) → ∀ w,
      Function.Surjective (ptLocalPairing ψ D M invr w (show 0 + 2 = 2 from rfl))
  /-- Every character of `H⁰(F_w, M')` vanishing on norms is a local pairing in degrees `(2, 0)`. -/
  surjective_realPairing_two : ∀ (M : Rep (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M],
    (∀ m : M, n • m = 0) → ∀ w
      (χ : cohomology (Rep.res (ψ w : F w →* G) (dualRep D M)) 0 →+ QZ),
      (∀ x ∈ normClasses (Rep.res (ψ w : F w →* G) (dualRep D M)), χ x = 0) →
      ∃ ξ, ptLocalPairing ψ D M invr w (show 2 + 0 = 2 from rfl) ξ = χ

variable (M : Rep (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M]

open Classical in
/-- The map `Hˢ(G, M')^∨ → Hʳ(G, M)` of the Tate-modified nine-term sequence (`r + s = 3`): the
inverse of the duality map followed by `Ĥ_c^r → Hʳ`; `0` when the duality map is not bijective
(under the hypotheses it is, for `r ≥ 1`: `ptTDualToGlobal_eq`). -/
noncomputable def ptTDualToGlobal {r s : ℕ} (h : r + s = 3) :
    (cohomology (dualRep D M) s →+ QZ) →+ cohomology M r :=
  if hb : Function.Bijective (ptTCompactDualMap φ ψ D M t h) then
    (ptTToGlobal φ ψ M r).hom.toAddMonoidHom.comp (AddEquiv.ofBijective _ hb).symm.toAddMonoidHom
  else 0

omit [Fintype ι] [Fintype κ] [NeZero n] in
theorem ptTDualToGlobal_eq {r s : ℕ} (h : r + s = 3)
    (hb : Function.Bijective (ptTCompactDualMap φ ψ D M t h)) :
    ptTDualToGlobal φ ψ D t M h =
      (ptTToGlobal φ ψ M r).hom.toAddMonoidHom.comp
        (AddEquiv.ofBijective _ hb).symm.toAddMonoidHom :=
  dite_eq_left hb

omit [Fintype ι] [Fintype κ] [IsSmoothRep D] in

theorem bijective_tateCompactCohomologyResMap_of_comp_eq_id {A B : Rep (ULift.{u} ℤ) G}
    [IsSmoothRep A] [IsSmoothRep B] (f : A ⟶ B) (g : B ⟶ A) (hfg : f ≫ g = 𝟙 A)
    (hgf : g ≫ f = 𝟙 B) (m : ℕ) : Function.Bijective (tateCompactCohomologyResMap φ ψ f m) := by
  refine Function.bijective_iff_has_inverse.2 ⟨tateCompactCohomologyResMap φ ψ g m, fun x => ?_,
    fun y => ?_⟩
  · rw [← ConcreteCategory.comp_apply, ← tateCompactCohomologyResMap_comp, hfg,
      tateCompactCohomologyResMap_id]
    rfl
  · rw [← ConcreteCategory.comp_apply, ← tateCompactCohomologyResMap_comp, hgf,
      tateCompactCohomologyResMap_id]
    rfl

/-- Exactness of the Tate-modified nine-term sequence: as `IsNineTermExact`, with Tate's `Ĥ⁰` at
the finite groups `F_w` in degree `0` (`ptTGlobalToLocalHat`, `ptTLocalHatDualMap`). -/
structure IsTateNineTermExact : Prop where
  injective_globalToLocalHat : Function.Injective (ptTGlobalToLocalHat φ ψ M)
  exact_globalToLocalHat :
    Function.Exact (ptTGlobalToLocalHat φ ψ M) (ptTLocalHatDualMap φ ψ D M inv invr)
  exact_localHatDualMap :
    Function.Exact (ptTLocalHatDualMap φ ψ D M inv invr)
      (ptTDualToGlobal φ ψ D t M (show 1 + 2 = 3 from rfl))
  exact_dualToGlobal_one :
    Function.Exact (ptTDualToGlobal φ ψ D t M (show 1 + 2 = 3 from rfl))
      (ptTGlobalToLocal φ ψ M 1).hom
  exact_globalToLocal_one :
    Function.Exact (ptTGlobalToLocal φ ψ M 1).hom
      (ptTLocalDualMap φ ψ D M inv invr (show 1 + 1 = 2 from rfl))
  exact_localDualMap_one :
    Function.Exact (ptTLocalDualMap φ ψ D M inv invr (show 1 + 1 = 2 from rfl))
      (ptTDualToGlobal φ ψ D t M (show 2 + 1 = 3 from rfl))
  exact_dualToGlobal_two :
    Function.Exact (ptTDualToGlobal φ ψ D t M (show 2 + 1 = 3 from rfl))
      (ptTGlobalToLocal φ ψ M 2).hom
  exact_globalToLocal_two :
    Function.Exact (ptTGlobalToLocal φ ψ M 2).hom
      (ptTLocalDualMap φ ψ D M inv invr (show 2 + 0 = 2 from rfl))
  surjective_localDualMap_two :
    Function.Surjective (ptTLocalDualMap φ ψ D M inv invr (show 2 + 0 = 2 from rfl))

namespace TatePoitouTateHypotheses

variable {φ ψ D t inv invr} (P : TatePoitouTateHypotheses φ ψ D t inv invr)

include P in

theorem bijective_ptTCompactDualMap (hM : ∀ m : M, n • m = 0) {r s : ℕ} (h : r + s = 3)
    (hr : 1 ≤ r) : Function.Bijective (ptTCompactDualMap φ ψ D M t h) := by
  have hD := P.nonempty_addEquiv
  have hnD := nsmul_eq_zero_of_nonempty_addEquiv hD
  have : Finite D := finite_of_nonempty_addEquiv hD
  have : Finite (dualRep D M) := finite_dualRep
  have : Finite (dualRep D (dualRep D M)) := finite_dualRep
  have : IsSmoothRep (dualRep D M) := isSmoothRep_dualRep D M
  have : IsSmoothRep (dualRep D (dualRep D M)) := isSmoothRep_dualRep D (dualRep D M)
  have hMD : ∀ f : dualRep D M, n • f = 0 := nsmul_dualRep_eq_zero hnD
  have hMDD : ∀ f : dualRep D (dualRep D M), n • f = 0 := nsmul_dualRep_eq_zero hnD
  have hφ := P.duality (dualRep D M) hMD (r := s) (s := r) (by omega) hr
  have : Finite (cohomology (dualRep D M) s) := P.finite_cohomology (dualRep D M) hMD s (by omega)
  have : Finite (tateCompactCohomologyRes φ ψ (dualRep D (dualRep D M)) r →+ ZMod n) :=
    Finite.of_surjective _ hφ.2
  have : Finite (tateCompactCohomologyRes φ ψ (dualRep D (dualRep D M)) r) :=
    finite_of_finite_addMonoidHom_zmod (nsmul_tateCompactCohomologyRes_eq_zero φ ψ hMDD r)
  have hflip := bijective_of_bijective_flip (nsmul_tateCompactCohomologyRes_eq_zero φ ψ hMDD r)
    (bilinAddHom (tateCompactCupRes φ ψ (dualEvalPairing D (dualRep D M)) h)) t hφ
  set e := repIsoOfBijective (toDualDual D M) (bijective_toDualDual hD hM)
  have hg := bijective_tateCompactCohomologyResMap_of_comp_eq_id φ ψ e.hom e.inv e.hom_inv_id
    e.inv_hom_id r
  have hμ : (toDualDual D M ⊗ₘ 𝟙 (dualRep D M)) ≫ dualEvalPairing D (dualRep D M) =
      (𝟙 M ⊗ₘ 𝟙 (dualRep D M)) ≫ evalPairing D M := by
    refine Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun z => ?_))
    induction z using TensorProduct.inductionOn with
    | tmul a f => rfl
    | add z z' hz hz' => simp only [map_add, hz, hz']
  let β : tateCompactCohomologyRes φ ψ M r →+ (cohomology (dualRep D M) s →+ ZMod n) :=
    (AddMonoidHom.compHom t).comp (bilinAddHom (tateCompactCupRes φ ψ (evalPairing D M) h))
  have hβ : Function.Bijective β := by
    convert hflip.comp hg using 1
    funext x
    refine AddMonoidHom.ext fun y => ?_
    change t (tateCompactCupRes φ ψ (evalPairing D M) h x y) =
      t (tateCompactCupRes φ ψ (dualEvalPairing D (dualRep D M)) h
        ((tateCompactCohomologyResMap φ ψ (toDualDual D M) r).hom x) y)
    rw [tateCompactCupRes_tateCompactCohomologyResMap φ ψ _ (evalPairing D M) _ (𝟙 _) hμ,
      coeffMap_id]
    rfl
  exact bijective_compHom_zmodToQZ β (nsmul_cohomology_eq_zero _ hMD s) hβ

omit [NeZero n] in
include P in

theorem ptTCompactDualMap_ptTLocalToCompact {r s : ℕ} (h : r + s = 2) (h' : r + 1 + s = 3)
    (ξ : ptTLocal φ ψ M r) :
    ptTCompactDualMap φ ψ D M t h' ((ptTLocalToCompact φ ψ M r).hom ξ) =
      ptTLocalDualMap φ ψ D M inv invr h ξ := by
  refine AddMonoidHom.ext fun y => ?_
  rw [ptTCompactDualMap_apply, tateCompactCupRes_ptTLocalToCompact φ ψ D M h h',
    P.localToCompact_two, ptTLocalDualMap_apply]
  rfl

include P in

theorem exact_stage_succ (hM : ∀ m : M, n • m = 0) {r s : ℕ} (h : r + 1 + s = 2)
    (h' : r + 1 + 1 + s = 3) :
    Function.Exact (ptTGlobalToLocal φ ψ M (r + 1)).hom (ptTLocalDualMap φ ψ D M inv invr h) ∧
      Function.Exact (ptTLocalDualMap φ ψ D M inv invr h)
        (ptTDualToGlobal φ ψ D t M h') ∧
      Function.Exact (ptTDualToGlobal φ ψ D t M h')
        (ptTGlobalToLocal φ ψ M (r + 1 + 1)).hom := by
  rw [ptTDualToGlobal_eq φ ψ D t M h' (P.bijective_ptTCompactDualMap M hM h' (by omega))]
  set e := AddEquiv.ofBijective _ (P.bijective_ptTCompactDualMap M hM h' (by omega))
  have hlam : ptTLocalDualMap φ ψ D M inv invr h =
      e.toAddMonoidHom.comp (ptTLocalToCompact φ ψ M (r + 1)).hom.toAddMonoidHom :=
    AddMonoidHom.ext fun ξ => (P.ptTCompactDualMap_ptTLocalToCompact M h h' ξ).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [hlam]
    exact exact_comp_addEquiv (ptTExact_local φ ψ M r) e
  · rw [hlam]
    exact exact_addEquiv_comp_comp_symm (g := (ptTLocalToCompact φ ψ M (r + 1)).hom.toAddMonoidHom)
      (ptTExact_compact φ ψ M (r + 1)) e
  · exact exact_comp_symm_addEquiv (ptTExact_global φ ψ M (r + 1)) e

end TatePoitouTateHypotheses

section DegreeZero

variable {φ ψ}

omit [Fintype ι] [Fintype κ] [Finite M] in

theorem exact_ptTLocalHatToCompact_ptTToGlobal :
    Function.Exact (ptTLocalHatToCompact φ ψ M) (ptTToGlobal φ ψ M 1).hom := fun z => by
  rw [ptTExact_compact φ ψ M 0 z]
  constructor
  · rintro ⟨ξ, rfl⟩
    exact ⟨ptTHatMk φ ψ M ξ, ptTLocalHatToCompact_hatMk φ ψ M ξ⟩
  · rintro ⟨ξ', rfl⟩
    obtain ⟨ξ, rfl⟩ := ptTHatMk_surjective φ ψ M ξ'
    exact ⟨ξ, (ptTLocalHatToCompact_hatMk φ ψ M ξ).symm⟩

omit [Fintype ι] [Fintype κ] [Finite M] in

theorem exact_ptTGlobalToLocalHat_ptTLocalHatToCompact :
    Function.Exact (ptTGlobalToLocalHat φ ψ M) (ptTLocalHatToCompact φ ψ M) := fun ξ' => by
  obtain ⟨ξ, rfl⟩ := ptTHatMk_surjective φ ψ M ξ'
  rw [ptTLocalHatToCompact_hatMk]
  have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (tateCompactCohomology_exact_localZero φ ψ M (fun v => Rep.res (φ v : Hv v →* G) M) (fun _ => 𝟙 _)
      (fun w => Rep.res (ψ w : F w →* G) M) (fun _ => 𝟙 _))
  constructor
  · intro h0
    obtain ⟨⟨x, e⟩, hxe⟩ := (hex ξ).1 h0
    refine ⟨x, ?_⟩
    rw [ptTGlobalToLocalHat_apply, ← sub_eq_zero, ← map_sub, ptTHatMk_eq_zero_iff]
    rw [← hxe, tateGlobalZeroToLocal_hom_apply, tateGlobalToLocal_hom_apply]
    refine ⟨sub_self _, fun w => ?_⟩
    change (globalToLocal ψ M _ (fun _ => 𝟙 _) 0).hom x w -
      ((globalToLocal ψ M _ (fun _ => 𝟙 _) 0).hom x w + normClass _ (e w)) ∈ _
    rw [sub_add_cancel_left]
    exact neg_mem (normClass_mem_normClasses _ (e w))
  · rintro ⟨x, hx⟩
    rw [ptTGlobalToLocalHat_apply, ← sub_eq_zero, ← map_sub] at hx
    have h1 := ptTLocalToCompact_of_hatMk_eq_zero φ ψ M _ hx
    rw [map_sub, sub_eq_zero] at h1
    rw [← h1]
    have hx0 : (tateGlobalZeroToLocal φ ψ M (fun v => Rep.res (φ v : Hv v →* G) M) (fun _ => 𝟙 _)
        (fun w => Rep.res (ψ w : F w →* G) M) (fun _ => 𝟙 _)).hom (x, 0) =
          (ptTGlobalToLocal φ ψ M 0).hom x := by
      rw [tateGlobalZeroToLocal_hom_apply, tateGlobalToLocal_hom_apply]
      refine Prod.ext rfl (funext fun w => ?_)
      change _ + normClass _ 0 = _
      rw [normClass_zero, add_zero]
    rw [← hx0]
    exact hom_apply_hom_apply_of_comp_eq (tateGlobalZeroToLocal_tateLocalToCompact φ ψ M _ _ _ _) _

end DegreeZero

namespace TatePoitouTateHypotheses

variable {φ ψ D t inv invr} (P : TatePoitouTateHypotheses φ ψ D t inv invr)

include P in

theorem exact_stage_zero (hM : ∀ m : M, n • m = 0) :
    Function.Exact (ptTGlobalToLocalHat φ ψ M) (ptTLocalHatDualMap φ ψ D M inv invr) ∧
      Function.Exact (ptTLocalHatDualMap φ ψ D M inv invr)
        (ptTDualToGlobal φ ψ D t M (show 1 + 2 = 3 from rfl)) ∧
      Function.Exact (ptTDualToGlobal φ ψ D t M (show 1 + 2 = 3 from rfl))
        (ptTGlobalToLocal φ ψ M 1).hom := by
  rw [ptTDualToGlobal_eq φ ψ D t M (show 1 + 2 = 3 from rfl)
    (P.bijective_ptTCompactDualMap M hM _ le_rfl)]
  set e := AddEquiv.ofBijective _ (P.bijective_ptTCompactDualMap M hM (show 1 + 2 = 3 from rfl) le_rfl)
  have hlam : ptTLocalHatDualMap φ ψ D M inv invr = e.toAddMonoidHom.comp (ptTLocalHatToCompact φ ψ M) :=
    AddMonoidHom.ext fun ξ' => by
      obtain ⟨ξ, rfl⟩ := ptTHatMk_surjective φ ψ M ξ'
      rw [ptTLocalHatDualMap_hatMk, AddMonoidHom.comp_apply, ptTLocalHatToCompact_hatMk]
      exact (P.ptTCompactDualMap_ptTLocalToCompact M (show 0 + 2 = 2 from rfl)
        (show 0 + 1 + 2 = 3 from rfl) ξ).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [hlam]
    exact exact_comp_addEquiv (exact_ptTGlobalToLocalHat_ptTLocalHatToCompact M) e
  · rw [hlam]
    exact exact_addEquiv_comp_comp_symm (g := ptTLocalHatToCompact φ ψ M)
      (exact_ptTLocalHatToCompact_ptTToGlobal M) e
  · exact exact_comp_symm_addEquiv (ptTExact_global φ ψ M 0) e

omit [NeZero n] [Finite M] in
include P in

theorem injective_ptTGlobalToLocalHat : Function.Injective (ptTGlobalToLocalHat φ ψ M) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => P.injective_res_zero M ?_
  have h1 := congrArg Prod.fst hx
  change (fun v => ptRes φ M v 0 x) = 0 at h1
  exact h1.trans (funext fun v => (map_zero (ptRes φ M v 0)).symm)

include P in

theorem surjective_ptTLocalDualMap_two (hM : ∀ m : M, n • m = 0) :
    Function.Surjective (ptTLocalDualMap φ ψ D M inv invr (show 2 + 0 = 2 from rfl)) := by
  classical
  have : Finite D := finite_of_nonempty_addEquiv P.nonempty_addEquiv
  have : Finite (dualRep D M) := finite_dualRep
  intro χ
  obtain ⟨g, hg⟩ := QZ.exists_comp_eq_of_injective (ptTGlobalToLocalHat φ ψ (dualRep D M))
    (P.injective_ptTGlobalToLocalHat (dualRep D M)) χ
  have hv : ∀ v, ∃ ξv, ptLocalPairing φ D M inv v (show 2 + 0 = 2 from rfl) ξv =
      g.comp ((AddMonoidHom.inl _ _).comp (AddMonoidHom.single
        (fun v => cohomology (Rep.res (φ v : Hv v →* G) (dualRep D M)) 0) v)) :=
    fun v => P.surjective_localPairing_two M hM v _
  have hw : ∀ w, ∃ ξw, ptLocalPairing ψ D M invr w (show 2 + 0 = 2 from rfl) ξw =
      g.comp ((AddMonoidHom.inr _ _).comp ((AddMonoidHom.single
        (fun w => cohomologyTateZero (Rep.res (ψ w : F w →* G) (dualRep D M))) w).comp
          (normClasses (Rep.res (ψ w : F w →* G) (dualRep D M))).mkQ.toAddMonoidHom)) :=
    fun w => P.surjective_realPairing_two M hM w _ fun x hx => by
      simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero _).2 hx, map_zero]
  choose ξ₁ hξ₁ using hv
  choose ξ₂ hξ₂ using hw
  refine ⟨(ξ₁, ξ₂), AddMonoidHom.ext fun y => ?_⟩
  have hdec : ptTGlobalToLocalHat φ ψ (dualRep D M) y =
      (∑ v, AddMonoidHom.inl _ _ (Pi.single v (ptRes φ (dualRep D M) v 0 y))) +
        ∑ w, AddMonoidHom.inr _ _
          (Pi.single w (Submodule.Quotient.mk (p := normClasses (Rep.res (ψ w : F w →* G) (dualRep D M)))
            (ptRes ψ (dualRep D M) w 0 y))) := by
    rw [ptTGlobalToLocalHat_apply, ptTGlobalToLocal_apply, ptTHatMk_apply, ← map_sum, ← map_sum]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, AddMonoidHom.inl_apply, AddMonoidHom.inr_apply, add_zero]
      exact (Finset.univ_sum_single _).symm
    · simp only [Prod.snd_add, AddMonoidHom.inl_apply, AddMonoidHom.inr_apply, zero_add]
      exact (Finset.univ_sum_single _).symm
  rw [ptTLocalDualMap_apply, ← hg, AddMonoidHom.comp_apply, hdec, map_add, map_sum, map_sum]
  congr 1
  · refine Finset.sum_congr rfl fun v _ => ?_
    rw [hξ₁]
    rfl
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [hξ₂]
    rfl

include P in

theorem surjective_ptTLocalToCompact_two (hM : ∀ m : M, n • m = 0) :
    Function.Surjective (ptTLocalToCompact φ ψ M 2).hom := fun z => by
  have hb := P.bijective_ptTCompactDualMap M hM (show 3 + 0 = 3 from rfl) (by norm_num)
  obtain ⟨ξ, hξ⟩ := P.surjective_ptTLocalDualMap_two M hM (ptTCompactDualMap φ ψ D M t _ z)
  refine ⟨ξ, hb.1 ?_⟩
  rw [P.ptTCompactDualMap_ptTLocalToCompact M (show 2 + 0 = 2 from rfl)
    (show 2 + 1 + 0 = 3 from rfl), hξ]

include P in

theorem injective_ptTGlobalToLocal_three (hM : ∀ m : M, n • m = 0) :
    Function.Injective (ptTGlobalToLocal φ ψ M 3).hom := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨z, rfl⟩ := (ptTExact_global φ ψ M 2 x).1 hx
  obtain ⟨ξ, rfl⟩ := P.surjective_ptTLocalToCompact_two M hM z
  exact (ptTExact_compact φ ψ M 2 _).2 ⟨ξ, rfl⟩

include P in
/-- The Tate-modified nine-term sequence of Poitou–Tate (abstract form). -/
theorem isTateNineTermExact (hM : ∀ m : M, n • m = 0) :
    IsTateNineTermExact φ ψ D t inv invr M := by
  obtain ⟨a0, b0, c0⟩ := P.exact_stage_zero M hM
  obtain ⟨a1, b1, c1⟩ := P.exact_stage_succ M hM (r := 0) (s := 1) rfl rfl
  obtain ⟨a2, -, -⟩ := P.exact_stage_succ M hM (r := 1) (s := 0) rfl rfl
  exact ⟨P.injective_ptTGlobalToLocalHat M, a0, b0, c0, a1, b1, c1, a2,
    P.surjective_ptTLocalDualMap_two M hM⟩

include P in

theorem bijective_ptTShaPairing (hM : ∀ m : M, n • m = 0) :
    Function.Bijective (ptTShaPairing φ ψ D M t) := by
  classical
  have hnD := nsmul_eq_zero_of_nonempty_addEquiv P.nonempty_addEquiv
  have : Finite D := finite_of_nonempty_addEquiv P.nonempty_addEquiv
  have : Finite (dualRep D M) := finite_dualRep
  have hψ := P.bijective_ptTCompactDualMap M hM (show 1 + 2 = 3 from rfl) le_rfl
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun χ => ?_⟩
  ·
    set f := ptTCompactDualMap φ ψ D M t (show 1 + 2 = 3 from rfl) (ptTShaLift φ ψ M x)
    have hker : (ptTGlobalToLocal φ ψ (dualRep D M) 2).hom.toAddMonoidHom.ker ≤ f.ker := fun y hy =>
      AddMonoidHom.mem_ker.2 (DFunLike.congr_fun hx ⟨y, hy⟩)
    obtain ⟨g, hg⟩ := QZ.exists_comp_eq_of_ker_le
      (ptTGlobalToLocal φ ψ (dualRep D M) 2).hom.toAddMonoidHom f hker
    have hv : ∀ v, ∃ ξv, ptLocalPairing φ D M inv v (show 0 + 2 = 2 from rfl) ξv =
        g.comp ((AddMonoidHom.inl _ _).comp (AddMonoidHom.single
          (fun v => cohomology (Rep.res (φ v : Hv v →* G) (dualRep D M)) 2) v)) :=
      fun v => P.surjective_localPairing_zero M hM v _
    have hw : ∀ w, ∃ ξw, ptLocalPairing ψ D M invr w (show 0 + 2 = 2 from rfl) ξw =
        g.comp ((AddMonoidHom.inr _ _).comp (AddMonoidHom.single
          (fun w => cohomology (Rep.res (ψ w : F w →* G) (dualRep D M)) 2) w)) :=
      fun w => P.surjective_realPairing_zero M hM w _
    choose ξ₁ hξ₁ using hv
    choose ξ₂ hξ₂ using hw
    have hf : ptTLocalDualMap φ ψ D M inv invr (show 0 + 2 = 2 from rfl) (ξ₁, ξ₂) = f := by
      refine AddMonoidHom.ext fun y => ?_
      have hdec : (ptTGlobalToLocal φ ψ (dualRep D M) 2).hom y =
          (∑ v, AddMonoidHom.inl _ _ (Pi.single v (ptRes φ (dualRep D M) v 2 y))) +
            ∑ w, AddMonoidHom.inr _ _ (Pi.single w (ptRes ψ (dualRep D M) w 2 y)) := by
        rw [ptTGlobalToLocal_apply, ← map_sum, ← map_sum]
        refine Prod.ext ?_ ?_
        · simp only [Prod.fst_add, AddMonoidHom.inl_apply, AddMonoidHom.inr_apply, add_zero]
          exact (Finset.univ_sum_single _).symm
        · simp only [Prod.snd_add, AddMonoidHom.inl_apply, AddMonoidHom.inr_apply, zero_add]
          exact (Finset.univ_sum_single _).symm
      rw [ptTLocalDualMap_apply, ← hg, AddMonoidHom.comp_apply]
      change _ = g ((ptTGlobalToLocal φ ψ (dualRep D M) 2).hom y)
      rw [hdec, map_add, map_sum, map_sum]
      congr 1
      · refine Finset.sum_congr rfl fun v _ => ?_
        rw [hξ₁]
        rfl
      · refine Finset.sum_congr rfl fun w _ => ?_
        rw [hξ₂]
        rfl
    rw [← P.ptTCompactDualMap_ptTLocalToCompact M _ (show 0 + 1 + 2 = 3 from rfl)] at hf
    have hx' : (ptTLocalToCompact φ ψ M 0).hom (ξ₁, ξ₂) = ptTShaLift φ ψ M x := hψ.1 hf
    apply Subtype.ext
    rw [← ptTToGlobal_ptTShaLift φ ψ M x, ← hx']
    exact (ptTExact_compact φ ψ M 0 _).2 ⟨(ξ₁, ξ₂), rfl⟩
  · obtain ⟨f, hf⟩ := QZ.exists_comp_eq_of_injective (ptTSha φ ψ (dualRep D M) 2).subtype
      Subtype.val_injective χ
    obtain ⟨x, hx⟩ := hψ.2 f
    refine ⟨⟨_, ptTToGlobal_mem_ptTSha φ ψ M (r := 0) x⟩, AddMonoidHom.ext fun y => ?_⟩
    rw [ptTShaPairing_apply, hx, ← hf]
    rfl

omit [NeZero n] in
include P in
/-- `Ш¹(M)` (with the real places) is finite. -/
theorem finite_ptTSha_one (hM : ∀ m : M, n • m = 0) : Finite (ptTSha φ ψ M 1) := by
  have := P.finite_cohomology M hM 1 (by norm_num)
  exact Finite.of_injective _ Subtype.val_injective

include P in
/-- `Ш²(M')` (with the real places) is finite. -/
theorem finite_ptTSha_two (_hM : ∀ m : M, n • m = 0) : Finite (ptTSha φ ψ (dualRep D M) 2) := by
  have hnD := nsmul_eq_zero_of_nonempty_addEquiv P.nonempty_addEquiv
  have : Finite D := finite_of_nonempty_addEquiv P.nonempty_addEquiv
  have : Finite (dualRep D M) := finite_dualRep
  have := P.finite_cohomology (dualRep D M) (nsmul_dualRep_eq_zero hnD) 2 le_rfl
  exact Finite.of_injective _ Subtype.val_injective

include P in
/-- The pairing of the two Tate–Shafarevich groups is perfect (flipped form). -/
theorem bijective_ptTShaPairing_flip (hM : ∀ m : M, n • m = 0) :
    Function.Bijective (ptTShaPairing φ ψ D M t).flip := by
  have := P.finite_ptTSha_one M hM
  have := P.finite_ptTSha_two M hM
  exact bijective_flip_of_bijective_qz _ (P.bijective_ptTShaPairing M hM)

end TatePoitouTateHypotheses

end Hypotheses

end

end RealAbstract

-- from PoitouTate/RealCup.lean
section RealCup

noncomputable section


open CategoryTheory MonoidalCategory


section LeibnizNatural

variable {k : Type u} [CommRing k] {M M' N P P' : CochainComplex (ModuleCat.{u} k) ℕ}

theorem LeibnizPairing.homologyMap_homology_of_comm (μ₁ : LeibnizPairing M N P)
    (μ₂ : LeibnizPairing M' N P') (f : M ⟶ M') (ψ : P ⟶ P')
    (hfψ : ∀ {r s n : ℕ} (h : r + s = n) (x : M.X r) (y : N.X s),
      (ψ.f n).hom (μ₁.μ h x y) = μ₂.μ h ((f.f r).hom x) y)
    {r s n : ℕ} (h : r + s = n) (x : M.homology r) (y : N.homology s) :
    (HomologicalComplex.homologyMap ψ n).hom (μ₁.homology h x y) =
      μ₂.homology h ((HomologicalComplex.homologyMap f r).hom x) y := by
  obtain ⟨x, rfl⟩ := homologyπ_hom_surjective M r x
  obtain ⟨y, rfl⟩ := homologyπ_hom_surjective N s y
  rw [hom_apply_hom_apply_eq_of_comp_eq (HomologicalComplex.homologyπ_naturality f r) x,
    LeibnizPairing.homology_homologyπ, LeibnizPairing.homology_homologyπ, homologyMap_homologyπ_apply]
  congr 1
  apply iCycles_hom_injective
  rw [LeibnizPairing.iCycles_cycles, iCycles_cyclesMap_apply, LeibnizPairing.iCycles_cycles,
    iCycles_cyclesMap_apply]
  exact hfψ h _ _

end LeibnizNatural

section Forget

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  {A B C : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B] [IsSmoothRep C]

/-- `tateForgetCochains` with the local modules the restrictions. -/
noncomputable abbrev tateForgetRes (A : Rep.{u} k G) [IsSmoothRep A] :=
  tateForgetCochains φ ψ A (fun v => Rep.res (φ v : H v →* G) A) (fun _ => 𝟙 _)
    (fun w => Rep.res (ψ w : F w →* G) A) (fun _ => 𝟙 _)

theorem tateForgetRes_cup (μ : A ⊗ B ⟶ C) {r s n : ℕ} (h : r + s = n)
    (p : (tateCompactCochains φ ψ A (fun v => Rep.res (φ v : H v →* G) A) (fun _ => 𝟙 _)
      (fun w => Rep.res (ψ w : F w →* G) A) (fun _ => 𝟙 _)).X r) (z : (cochains B).X s) :
    ((tateForgetRes φ ψ C).f n).hom ((tateCompactCupResLeibniz φ ψ μ).μ h p z) =
      (compactCupLeibniz φ μ (fun v => (Rep.resFunctor (φ v : H v →* G)).map μ)
        (fun v => resFunctor_map_comp_id (φ v : H v →* G) μ)).μ h (((tateForgetRes φ ψ A).f r).hom p) z := by
  revert p
  intro (p : (tateGlobalComplex A fun w => Rep.res (ψ w : F w →* G) A).X r ×
    shiftNegOneX (tateLocalComplex (fun v => Rep.res (φ v : H v →* G) A)
      fun w => Rep.res (ψ w : F w →* G) A) r)
  obtain ⟨⟨x, e⟩, b⟩ := p
  refine Prod.ext rfl ?_
  rcases r with _ | r
  · rcases n with _ | n
    · rfl
    · change (prodFst _ _ |>.f n).hom (0 + tateCupHomotopyL ψ
          (fun w => (Rep.resFunctor (ψ w : F w →* G)).map μ)
          (Cᵥ := fun v => Rep.res (φ v : H v →* G) C) (by omega) e z) = 0
      rw [zero_add]
      erw [tateCupHomotopyL_apply]
      rfl
  · rcases n with _ | n
    · omega
    · change (prodFst _ _ |>.f n).hom ((tateLocalCup φ ψ (fun v => (Rep.resFunctor (φ v : H v →* G)).map μ)
          (fun w => (Rep.resFunctor (ψ w : F w →* G)).map μ)).μ (show r + s = n by omega) b
          (((tateLocalResB φ ψ B).f s).hom z) + 0) = _
      rw [add_zero]
      rfl

theorem tateForget_tateCompactCupRes (μ : A ⊗ B ⟶ C) {r s n : ℕ} (h : r + s = n)
    (x : tateCompactCohomologyRes φ ψ A r) (z : cohomology B s) :
    (tateForget φ ψ C (fun v => Rep.res (φ v : H v →* G) C) (fun _ => 𝟙 _)
        (fun w => Rep.res (ψ w : F w →* G) C) (fun _ => 𝟙 _) n).hom (tateCompactCupRes φ ψ μ h x z) =
      compactCupRes φ μ h ((tateForget φ ψ A (fun v => Rep.res (φ v : H v →* G) A) (fun _ => 𝟙 _)
        (fun w => Rep.res (ψ w : F w →* G) A) (fun _ => 𝟙 _) r).hom x) z :=
  LeibnizPairing.homologyMap_homology_of_comm _ _ _ _ (fun h p z => tateForgetRes_cup φ ψ μ h p z) h x z

end Forget

section Target

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  {A B C C' : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B] [IsSmoothRep C] [IsSmoothRep C']

omit [IsTopologicalGroup G] in

theorem cochainsMap_normHomotopy {F' : Type u} [Group F'] [TopologicalSpace F'] [IsTopologicalGroup F'] [Fintype F'] {X Y Z Z' : Rep.{u} k F'}
    [IsSmoothRep Y] [IsSmoothRep Z] [IsSmoothRep Z'] (μ : X ⊗ Y ⟶ Z) (g : Z ⟶ Z')
    {s m : ℕ} (h : s = m + 1) (e : X) (y : (cochains Y).X s) :
    ((coeffCochainsMap g).f m).hom (normHomotopy μ h e y) = normHomotopy (μ ≫ g) h e y := by
  apply cochainOf_injective
  funext σ
  rw [cochainOf_normHomotopy]
  change g.hom (cochainOf Z (normHomotopy μ h e y) σ) = _
  rw [cochainOf_normHomotopy]
  change g.hom (∑ a : F', Z.ρ a (μ.hom _)) = ∑ a : F', Z'.ρ a (g.hom (μ.hom _))
  rw [map_sum]
  exact Finset.sum_congr rfl fun a _ => Rep.hom_comm_apply g a _

theorem tateCompactCochainsResMap_cup (μ : A ⊗ B ⟶ C) (g : C ⟶ C') {r s n : ℕ} (h : r + s = n)
    (p : (tateCompactCochains φ ψ A (fun v => Rep.res (φ v : H v →* G) A) (fun _ => 𝟙 _)
      (fun w => Rep.res (ψ w : F w →* G) A) (fun _ => 𝟙 _)).X r) (z : (cochains B).X s) :
    ((tateCompactCochainsResMap φ ψ g).f n).hom ((tateCompactCupResLeibniz φ ψ μ).μ h p z) =
      (tateCompactCupResLeibniz φ ψ (μ ≫ g)).μ h p z := by
  revert p
  intro (p : (tateGlobalComplex A fun w => Rep.res (ψ w : F w →* G) A).X r ×
    shiftNegOneX (tateLocalComplex (fun v => Rep.res (φ v : H v →* G) A)
      fun w => Rep.res (ψ w : F w →* G) A) r)
  obtain ⟨⟨x, e⟩, b⟩ := p
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · apply cochainOf_injective
    rfl
  · rcases r with _ | r
    · rcases s with _ | s
      · obtain rfl : n = 0 := by omega
        rfl
      · obtain rfl : n = s + 1 := by omega
        exact Subsingleton.elim _ _
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨r + s, by omega⟩
      exact Subsingleton.elim _ _
  · rcases r with _ | r
    · rcases s with _ | t
      · obtain rfl : n = 0 := by omega
        exact Subsingleton.elim (α := PUnit) _ _
      · obtain rfl : n = t + 1 := by omega
        change ((tateLocalMap (fun v => (Rep.resFunctor (φ v : H v →* G)).map g)
            (fun w => (Rep.resFunctor (ψ w : F w →* G)).map g)).f t).hom
            ((0 : (tateLocalComplex (fun v => Rep.res (φ v : H v →* G) C)
              fun w => Rep.res (ψ w : F w →* G) C).X t) +
            tateCupHomotopyL ψ (fun w => (Rep.resFunctor (ψ w : F w →* G)).map μ)
              (Cᵥ := fun v => Rep.res (φ v : H v →* G) C) (rfl : t + 1 = t + 1) e z) =
          (0 : (tateLocalComplex (fun v => Rep.res (φ v : H v →* G) C')
              fun w => Rep.res (ψ w : F w →* G) C').X t) +
            tateCupHomotopyL ψ (fun w => (Rep.resFunctor (ψ w : F w →* G)).map (μ ≫ g))
              (Cᵥ := fun v => Rep.res (φ v : H v →* G) C') (rfl : t + 1 = t + 1) e z
        rw [zero_add, zero_add]
        erw [tateCupHomotopyL_apply, tateCupHomotopyL_apply]
        refine Prod.ext ?_ (funext fun w => ?_)
        · change ((piMap fun v => coeffCochainsMap ((Rep.resFunctor (φ v : H v →* G)).map g)).f t).hom 0 = 0
          exact map_zero _
        change ((coeffCochainsMap ((Rep.resFunctor (ψ w : F w →* G)).map g)).f t).hom
          (-(tateNormHomotopy ψ (fun w => (Rep.resFunctor (ψ w : F w →* G)).map μ) rfl e z w)) =
            -(tateNormHomotopy ψ (fun w => (Rep.resFunctor (ψ w : F w →* G)).map (μ ≫ g)) rfl e z w)
        rw [map_neg]
        exact congrArg Neg.neg (cochainsMap_normHomotopy _ _ _ _ _)
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨r + s, by omega⟩
      change ((tateLocalMap (fun v => (Rep.resFunctor (φ v : H v →* G)).map g)
            (fun w => (Rep.resFunctor (ψ w : F w →* G)).map g)).f m).hom
          ((tateLocalCup φ ψ (fun v => (Rep.resFunctor (φ v : H v →* G)).map μ)
            (fun w => (Rep.resFunctor (ψ w : F w →* G)).map μ)).μ (show r + s = m by omega) b
            (((tateLocalResB φ ψ B).f s).hom z) + 0) =
          (tateLocalCup φ ψ (fun v => (Rep.resFunctor (φ v : H v →* G)).map (μ ≫ g))
            (fun w => (Rep.resFunctor (ψ w : F w →* G)).map (μ ≫ g))).μ (show r + s = m by omega) b
            (((tateLocalResB φ ψ B).f s).hom z) + 0
      rw [add_zero, add_zero]
      refine Prod.ext (funext fun v => ?_) (funext fun w => ?_)
      · apply cochainOf_injective
        rfl
      · apply cochainOf_injective
        rfl

theorem tateCompactCohomologyResMap_tateCompactCupRes (μ : A ⊗ B ⟶ C) (g : C ⟶ C') {r s n : ℕ}
    (h : r + s = n) (x : tateCompactCohomologyRes φ ψ A r) (z : cohomology B s) :
    (tateCompactCohomologyResMap φ ψ g n).hom (tateCompactCupRes φ ψ μ h x z) =
      tateCompactCupRes φ ψ (μ ≫ g) h x z := by
  have e := LeibnizPairing.homologyMap_homology_of_comm (tateCompactCupResLeibniz φ ψ μ)
    (tateCompactCupResLeibniz φ ψ (μ ≫ g)) (𝟙 _) (tateCompactCochainsResMap φ ψ g)
    (fun h p z => tateCompactCochainsResMap_cup φ ψ μ g h p z) h x z
  rw [HomologicalComplex.homologyMap_id] at e
  exact e

end Target

end

end RealCup

end Langlands.GaloisCohomology
