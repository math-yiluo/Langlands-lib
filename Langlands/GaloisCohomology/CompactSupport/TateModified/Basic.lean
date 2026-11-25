import Langlands.GaloisCohomology.CompactSupport.Functoriality
import Langlands.GaloisCohomology.CompactSupport.Internal.LeibnizPairing
import Langlands.Cohomology.Profinite.Cyclic.Cup
import Langlands.Cohomology.Profinite.LowDegree

/-!
# Cohomology with compact support modified at a family of finite groups

In addition to the family `(φ_v : H_v →ₜ* G)`, let `(ψ_w : F_w →ₜ* G)` be a family of finite groups
with modules `A_w` (for `G_S`: the decomposition groups `Gal(ℂ/ℝ)` at the real places). The global
term of the cocone becomes `C•(G, A) × ∏_w A_w` (the second factor in degree `0`) and the map to
the local term adds the norm cochains `m_w ↦ N_{F_w} m_w`; its cocone `tateCompactCochains` has
cohomology `Ĥ_c^n(G, A)`, in which degree `0` at the `F_w` is Tate's `Ĥ⁰` (`cohomologyTateZero`). The
long exact sequence `⋯ → Ĥ_c^n → Hⁿ(G) → ∏_v Hⁿ(H_v) × ∏_w Hⁿ(F_w) → Ĥ_c^{n+1} → ⋯` (for `n ≥ 1`;
in degree `0` with `H⁰(G) × ∏_w A_w`), the functoriality in the module and the connecting map of a
short exact sequence are proved as for ordinary compact support.
-/

namespace Langlands.GaloisCohomology

open Langlands Langlands.ProfiniteCohomology

universe u

-- from RealPlaces/LocalDualityDefs.lean (TateZero)
section TateZeroDefs

open CategoryTheory

section TateZero

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Fintype G]

/-- The classes of norms in `H⁰(F, A) = A^F`, for a finite group `F`. -/
noncomputable def normClasses (A : Rep k G) [IsSmoothRep A] : Submodule k (cohomology A 0) :=
  (Langlands.Tate.normImage A).map (zeroIso A).inv.hom

theorem mem_normClasses_iff (A : Rep k G) [IsSmoothRep A] (x : cohomology A 0) :
    x ∈ normClasses A ↔ ∃ a : A, ∃ h : A.ρ.norm a ∈ A.ρ.invariants,
      x = (zeroIso A).inv.hom ⟨A.ρ.norm a, h⟩ := by
  constructor
  · rintro ⟨y, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, (Langlands.Tate.normToInvariants A a).2, rfl⟩
  · rintro ⟨a, h, rfl⟩
    exact ⟨⟨A.ρ.norm a, h⟩, ⟨a, rfl⟩, rfl⟩

/-- Tate's `Ĥ⁰(F, A) = H⁰(F, A) / norms`, for a finite group `F`. -/
abbrev cohomologyTateZero (A : Rep k G) [IsSmoothRep A] : Type u :=
  cohomology A 0 ⧸ normClasses A

end TateZero

end TateZeroDefs

-- from RealPlaces/ConeDefs.lean
section ConeDefs

open CategoryTheory Limits


section Prod

variable {k : Type u} [CommRing k]

/-- The product of two `ℕ`-indexed complexes of modules, degreewise. -/
noncomputable def prodComplex (M N : CochainComplex (ModuleCat.{u} k) ℕ) :
    CochainComplex (ModuleCat.{u} k) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of k (M.X n × N.X n))
    (fun n => ModuleCat.ofHom ((M.d n (n + 1)).hom.prodMap (N.d n (n + 1)).hom))
    fun _ => ModuleCat.hom_ext (LinearMap.ext fun x => Prod.ext
      (hom_apply_hom_apply_of_comp_eq (M.d_comp_d _ _ _) x.1)
      (hom_apply_hom_apply_of_comp_eq (N.d_comp_d _ _ _) x.2))

variable (M N : CochainComplex (ModuleCat.{u} k) ℕ)

theorem prodComplex_d (n : ℕ) :
    (prodComplex M N).d n (n + 1) =
      ModuleCat.ofHom ((M.d n (n + 1)).hom.prodMap (N.d n (n + 1)).hom) := by
  unfold prodComplex
  exact CochainComplex.of_d (V := ModuleCat.{u} k) (fun n => ModuleCat.of k (M.X n × N.X n))
    (fun n => ModuleCat.ofHom ((M.d n (n + 1)).hom.prodMap (N.d n (n + 1)).hom)) n

theorem prodComplex_d_hom_apply (n : ℕ) (x : (prodComplex M N).X n) :
    ((prodComplex M N).d n (n + 1)).hom x =
      (((M.d n (n + 1)).hom x.1, (N.d n (n + 1)).hom x.2) : M.X (n + 1) × N.X (n + 1)) := by
  rw [prodComplex_d]
  rfl

theorem prodComplex_d_hom_apply' (i j : ℕ) (x : (prodComplex M N).X i) :
    ((prodComplex M N).d i j).hom x =
      (((M.d i j).hom x.1, (N.d i j).hom x.2) : M.X j × N.X j) := by
  by_cases h : i + 1 = j
  · subst h
    exact prodComplex_d_hom_apply M N i x
  · rw [(prodComplex M N).shape i j h, M.shape i j h, N.shape i j h]
    rfl

/-- The first projection of the product complex. -/
noncomputable def prodFst : prodComplex M N ⟶ M :=
  CochainComplex.ofHom (fun _ => ModuleCat.ofHom (LinearMap.fst k _ _)) fun n =>
    ModuleCat.hom_ext (LinearMap.ext fun x => (congrArg Prod.fst (prodComplex_d_hom_apply M N n x)).symm)

/-- The second projection of the product complex. -/
noncomputable def prodSnd : prodComplex M N ⟶ N :=
  CochainComplex.ofHom (fun _ => ModuleCat.ofHom (LinearMap.snd k _ _)) fun n =>
    ModuleCat.hom_ext (LinearMap.ext fun x => (congrArg Prod.snd (prodComplex_d_hom_apply M N n x)).symm)

variable {M N}

/-- The morphism into the product complex given by two morphisms. -/
noncomputable def prodLift {P : CochainComplex (ModuleCat.{u} k) ℕ} (f : P ⟶ M) (g : P ⟶ N) :
    P ⟶ prodComplex M N :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom ((f.f n).hom.prod (g.f n).hom)) fun n =>
    ModuleCat.hom_ext (LinearMap.ext fun x => by
      change ((prodComplex M N).d n (n + 1)).hom
          (show (prodComplex M N).X n from ((f.f n).hom x, (g.f n).hom x)) =
        ((f.f (n + 1)).hom ((P.d n (n + 1)).hom x), (g.f (n + 1)).hom ((P.d n (n + 1)).hom x))
      refine (prodComplex_d_hom_apply M N n _).trans ?_
      exact Prod.ext (hom_apply_hom_apply_eq_of_comp_eq (f.comm n (n + 1)) x)
        (hom_apply_hom_apply_eq_of_comp_eq (g.comm n (n + 1)) x))

@[reassoc (attr := simp)]
theorem prodLift_prodFst {P : CochainComplex (ModuleCat.{u} k) ℕ} (f : P ⟶ M) (g : P ⟶ N) :
    prodLift f g ≫ prodFst M N = f :=
  HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

@[reassoc (attr := simp)]
theorem prodLift_prodSnd {P : CochainComplex (ModuleCat.{u} k) ℕ} (f : P ⟶ M) (g : P ⟶ N) :
    prodLift f g ≫ prodSnd M N = g :=
  HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

/-- The product of two morphisms of complexes. -/
noncomputable def prodMapCx {M' N' : CochainComplex (ModuleCat.{u} k) ℕ} (f : M ⟶ M') (g : N ⟶ N') :
    prodComplex M N ⟶ prodComplex M' N' :=
  prodLift (prodFst M N ≫ f) (prodSnd M N ≫ g)

end Prod

section DegZero

variable {k : Type u} [CommRing k]

/-- The terms of the complex concentrated in degree `0`. -/
noncomputable def degZeroX (E : ModuleCat.{u} k) : ℕ → ModuleCat.{u} k
  | 0 => E
  | _ + 1 => ModuleCat.of k PUnit

/-- A module viewed as a complex concentrated in degree `0`. -/
noncomputable def degZeroComplex (E : ModuleCat.{u} k) : CochainComplex (ModuleCat.{u} k) ℕ :=
  CochainComplex.of (degZeroX E) (fun _ => 0) fun _ => Limits.zero_comp

theorem degZeroComplex_d (E : ModuleCat.{u} k) (i j : ℕ) : (degZeroComplex E).d i j = 0 := by
  by_cases h : i + 1 = j
  · subst h
    exact CochainComplex.of_d (V := ModuleCat.{u} k) (degZeroX E) (fun _ => 0) i
  · exact (degZeroComplex E).shape i j h

instance (E : ModuleCat.{u} k) (n : ℕ) : Subsingleton ((degZeroComplex E).X (n + 1)) :=
  inferInstanceAs (Subsingleton PUnit)

end DegZero

section Norm

variable {k F : Type u} [CommRing k] [Group F] [TopologicalSpace F] [IsTopologicalGroup F]

/-- A vector as a `0`-cochain. -/
noncomputable def zeroCochain (B : Rep.{u} k F) [IsSmoothRep B] : B →ₗ[k] (cochains B).X 0 where
  toFun m := mkCochain B (fun _ => m) (IsLocallyConstant.const m)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem cochainOf_zeroCochain (B : Rep.{u} k F) [IsSmoothRep B] (m : B) (σ : Fin 0 → F) :
    cochainOf B (zeroCochain B m) σ = m :=
  rfl

theorem cochainOf_d_zeroCochain (B : Rep.{u} k F) [IsSmoothRep B] (m : B) (σ : Fin 1 → F) :
    cochainOf B (((cochains B).d 0 1).hom (zeroCochain B m)) σ = B.ρ (σ 0) m - m := by
  rw [cochainOf_d]
  simp [inhomogeneousCochains.d_hom_apply, cochainOf_zeroCochain, sub_eq_add_neg]

variable [Fintype F]

theorem d_zeroCochain_norm (B : Rep.{u} k F) [IsSmoothRep B] (m : B) :
    ((cochains B).d 0 1).hom (zeroCochain B (B.ρ.norm m)) = 0 := by
  apply cochainOf_injective
  funext σ
  rw [cochainOf_d_zeroCochain, Representation.self_norm_apply, sub_self]
  rfl

end Norm

section Tate

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)

section Norm

variable (Aᵣ : ∀ w, Rep.{u} k (F w)) [∀ w, IsSmoothRep (Aᵣ w)]

/-- The components of `normCochains`. -/
noncomputable def normCochainsF : ∀ n, (degZeroComplex (ModuleCat.of k (∀ w, Aᵣ w))).X n ⟶
    (piComplex fun w => cochains (Aᵣ w)).X n
  | 0 => ModuleCat.ofHom (LinearMap.pi fun w =>
      (zeroCochain (Aᵣ w)).comp ((Aᵣ w).ρ.norm.comp (LinearMap.proj w)))
  | _ + 1 => 0

theorem normCochainsF_zero_apply (e : (degZeroComplex (ModuleCat.of k (∀ w, Aᵣ w))).X 0)
    (w : κ) :
    (normCochainsF Aᵣ 0).hom e w = zeroCochain (Aᵣ w) ((Aᵣ w).ρ.norm ((show ∀ w, Aᵣ w from e) w)) :=
  rfl

/-- The map `∏_w A_w → ∏_w C•(F_w, A_w)` (in degree `0`) sending `(m_w)` to the `0`-cochains of
the norms `N_{F_w} m_w`. -/
noncomputable def normCochains :
    degZeroComplex (ModuleCat.of k (∀ w, Aᵣ w)) ⟶ piComplex fun w => cochains (Aᵣ w) :=
  CochainComplex.ofHom (normCochainsF Aᵣ) fun n => by
    cases n with
    | zero =>
      refine ModuleCat.hom_ext (LinearMap.ext fun e => funext fun w => ?_)
      rw [degZeroComplex_d]
      change ((piComplex fun w => cochains (Aᵣ w)).d 0 1).hom
        ((normCochainsF Aᵣ 0).hom e) w = 0
      rw [piComplex_d_hom_apply, normCochainsF_zero_apply]
      exact d_zeroCochain_norm (Aᵣ w) _
    | succ n =>
      change (0 : _ ⟶ _) ≫ _ = _ ≫ (0 : _ ⟶ _)
      rw [zero_comp, comp_zero]

end Norm

variable (A : Rep.{u} k G) [IsSmoothRep A] (Aᵥ : ∀ v, Rep.{u} k (H v))
  [∀ v, IsSmoothRep (Aᵥ v)] (a : ∀ v, Rep.res (φ v : H v →* G) A ⟶ Aᵥ v)
  (Aᵣ : ∀ w, Rep.{u} k (F w)) [∀ w, IsSmoothRep (Aᵣ w)]
  (ar : ∀ w, Rep.res (ψ w : F w →* G) A ⟶ Aᵣ w)

/-- The global term of the Tate-modified cocone: `C•(G, A) × ∏_w A_w` (the second factor in degree
`0`). -/
noncomputable abbrev tateGlobalComplex : CochainComplex (ModuleCat.{u} k) ℕ :=
  prodComplex (cochains A) (degZeroComplex (ModuleCat.of k (∀ w, Aᵣ w)))

/-- The local term of the Tate-modified cocone: `∏_v C•(H_v, A_v) × ∏_w C•(F_w, A_w)`. -/
noncomputable abbrev tateLocalComplex : CochainComplex (ModuleCat.{u} k) ℕ :=
  prodComplex (piComplex fun v => cochains (Aᵥ v)) (piComplex fun w => cochains (Aᵣ w))

/-- The map of the Tate-modified cocone: restriction to all local groups, plus the norm cochains
at the finite groups `F_w`. -/
noncomputable def tateCompactRes : tateGlobalComplex A Aᵣ ⟶ tateLocalComplex Aᵥ Aᵣ :=
  prodLift (prodFst _ _ ≫ localRes φ A Aᵥ a)
    (prodFst _ _ ≫ localRes ψ A Aᵣ ar + prodSnd _ _ ≫ normCochains Aᵣ)

/-- The Tate-modified cochains with compact support: the mapping cocone of `tateCompactRes`. -/
noncomputable def tateCompactCochains : CochainComplex (ModuleCat.{u} k) ℕ :=
  mappingCoconeNat (tateCompactRes φ ψ A Aᵥ a Aᵣ ar)

/-- The Tate-modified cohomology with compact support `Ĥ_c^n(G, A)`, in which degree `0` at the
finite groups `F_w` is replaced by Tate's `Ĥ⁰`. -/
noncomputable def tateCompactCohomology (n : ℕ) : ModuleCat.{u} k :=
  (tateCompactCochains φ ψ A Aᵥ a Aᵣ ar).homology n

/-- `Ĥ_c^n(G, A)` when the local modules are the restrictions of `A`. -/
noncomputable abbrev tateCompactCohomologyRes (n : ℕ) : ModuleCat.{u} k :=
  tateCompactCohomology φ ψ A (fun v => Rep.res (φ v : H v →* G) A) (fun _ => 𝟙 _)
    (fun w => Rep.res (ψ w : F w →* G) A) (fun _ => 𝟙 _) n

end Tate

end ConeDefs

-- from RealPlaces/LocalCohomologyIsoHomologyMapNormCochains.lean
section LocalCohomologyIsoHomologyMapNormCochains

open CategoryTheory Limits


section ProdHomology

variable {k : Type u} [CommRing k] (M N : CochainComplex (ModuleCat.{u} k) ℕ)

/-- The comparison map from the homology of a product complex to the product of the homologies. -/
noncomputable def prodHomologyToProd (n : ℕ) :
    (prodComplex M N).homology n ⟶ ModuleCat.of k (M.homology n × N.homology n) :=
  ModuleCat.ofHom ((HomologicalComplex.homologyMap (prodFst M N) n).hom.prod
    (HomologicalComplex.homologyMap (prodSnd M N) n).hom)

theorem prodHomologyToProd_bijective (n : ℕ) :
    Function.Bijective (prodHomologyToProd M N n).hom := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro h hh
    obtain ⟨c, rfl⟩ :=
      (ModuleCat.epi_iff_surjective ((prodComplex M N).homologyπ n)).1 inferInstance h
    have h1 : ∃ y : M.X ((ComplexShape.up ℕ).prev n), (M.d _ n).hom y =
        (M.iCycles n).hom ((HomologicalComplex.cyclesMap (prodFst M N) n).hom c) := by
      refine (homologyπ_eq_zero_iff _ _).1 ?_
      rw [← homologyMap_homologyπ_apply]
      exact congrArg Prod.fst hh
    have h2 : ∃ y : N.X ((ComplexShape.up ℕ).prev n), (N.d _ n).hom y =
        (N.iCycles n).hom ((HomologicalComplex.cyclesMap (prodSnd M N) n).hom c) := by
      refine (homologyπ_eq_zero_iff _ _).1 ?_
      rw [← homologyMap_homologyπ_apply]
      exact congrArg Prod.snd hh
    obtain ⟨y1, hy1⟩ := h1
    obtain ⟨y2, hy2⟩ := h2
    refine (homologyπ_eq_zero_iff _ c).2 ⟨show (prodComplex M N).X _ from (y1, y2), ?_⟩
    rw [prodComplex_d_hom_apply', hy1, hy2, iCycles_cyclesMap_apply, iCycles_cyclesMap_apply]
    rfl
  · rintro ⟨h1, h2⟩
    obtain ⟨c1, hc1⟩ := (ModuleCat.epi_iff_surjective (M.homologyπ n)).1 inferInstance h1
    obtain ⟨c2, hc2⟩ := (ModuleCat.epi_iff_surjective (N.homologyπ n)).1 inferInstance h2
    obtain ⟨c', hc'⟩ := exists_iCycles_eq (K := prodComplex M N)
      (show (prodComplex M N).X n from ((M.iCycles n).hom c1, (N.iCycles n).hom c2)) (by
        rw [CochainComplex.next, prodComplex_d_hom_apply]
        exact Prod.ext (iCycles_d_apply _ n (n + 1) c1) (iCycles_d_apply _ n (n + 1) c2))
    refine ⟨((prodComplex M N).homologyπ n).hom c', Prod.ext ?_ ?_⟩
    · change (HomologicalComplex.homologyMap (prodFst M N) n).hom _ = h1
      rw [homologyMap_homologyπ_apply, ← hc1]
      congr 1
      apply (ModuleCat.mono_iff_injective (M.iCycles n)).1 inferInstance
      rw [iCycles_cyclesMap_apply, hc']
      rfl
    · change (HomologicalComplex.homologyMap (prodSnd M N) n).hom _ = h2
      rw [homologyMap_homologyπ_apply, ← hc2]
      congr 1
      apply (ModuleCat.mono_iff_injective (N.iCycles n)).1 inferInstance
      rw [iCycles_cyclesMap_apply, hc']
      rfl

/-- The homology of a product of two complexes is the product of the homologies. -/
noncomputable def prodHomologyIso (n : ℕ) :
    (prodComplex M N).homology n ≅ ModuleCat.of k (M.homology n × N.homology n) :=
  (LinearEquiv.ofBijective (prodHomologyToProd M N n).hom
    (prodHomologyToProd_bijective M N n)).toModuleIso

theorem isIso_homologyMap_prodFst {n : ℕ} (hN : IsZero (N.homology n)) :
    IsIso (HomologicalComplex.homologyMap (prodFst M N) n) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  have hb := prodHomologyToProd_bijective M N n
  constructor
  · intro x y hxy
    refine hb.1 (Prod.ext hxy ?_)
    exact (ModuleCat.subsingleton_of_isZero hN).elim _ _
  · intro m
    obtain ⟨h, hh⟩ := hb.2 (m, 0)
    exact ⟨h, congrArg Prod.fst hh⟩

end ProdHomology

section DegZeroHomology

variable {k : Type u} [CommRing k] (E : ModuleCat.{u} k)

theorem isZero_degZeroComplex_homology_succ (n : ℕ) :
    IsZero ((degZeroComplex E).homology (n + 1)) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _
    (ModuleCat.isZero_of_subsingleton ((degZeroComplex E).X (n + 1)))

/-- The homology in degree `0` of a module concentrated in degree `0`. -/
noncomputable def degZeroHomologyIso : (degZeroComplex E).homology 0 ≅ E :=
  (degZeroComplex E).isoHomologyπ₀.symm ≪≫
    (degZeroComplex E).iCyclesIso 0 1 (by simp) (degZeroComplex_d E 0 1)

theorem degZeroHomologyIso_hom_homologyπ (c : (degZeroComplex E).cycles 0) :
    (degZeroHomologyIso E).hom.hom (((degZeroComplex E).homologyπ 0).hom c) =
      ((degZeroComplex E).iCycles 0).hom c := by
  change ((degZeroComplex E).iCycles 0).hom
      ((degZeroComplex E).isoHomologyπ₀.inv.hom (((degZeroComplex E).homologyπ 0).hom c)) = _
  rw [hom_apply_hom_apply_of_comp_eq
    (HomologicalComplex.isoHomologyπ_hom_inv_id (degZeroComplex E) _ 0 rfl (by simp)) c]
  rfl

end DegZeroHomology

section Tate

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  (A : Rep.{u} k G) [IsSmoothRep A] (Aᵥ : ∀ v, Rep.{u} k (H v))
  [∀ v, IsSmoothRep (Aᵥ v)] (a : ∀ v, Rep.res (φ v : H v →* G) A ⟶ Aᵥ v)
  (Aᵣ : ∀ w, Rep.{u} k (F w)) [∀ w, IsSmoothRep (Aᵣ w)]
  (ar : ∀ w, Rep.res (ψ w : F w →* G) A ⟶ Aᵣ w)

section Terms

/-- The homology of the local term is the product of the local cohomology groups. -/
noncomputable def tateLocalCohomologyIso (n : ℕ) :
    (tateLocalComplex Aᵥ Aᵣ).homology n ≅
      ModuleCat.of k ((∀ v, cohomology (Aᵥ v) n) × (∀ w, cohomology (Aᵣ w) n)) :=
  prodHomologyIso _ _ n ≪≫
    ((localCohomologyIso Aᵥ n).toLinearEquiv.prodCongr (localCohomologyIso Aᵣ n).toLinearEquiv).toModuleIso

omit [∀ w, Fintype (F w)] in
theorem tateLocalCohomologyIso_hom_apply (n : ℕ) (z : (tateLocalComplex Aᵥ Aᵣ).homology n) :
    (tateLocalCohomologyIso Aᵥ Aᵣ n).hom.hom z =
      ((localCohomologyIso Aᵥ n).hom.hom ((HomologicalComplex.homologyMap (prodFst _ _) n).hom z),
        (localCohomologyIso Aᵣ n).hom.hom ((HomologicalComplex.homologyMap (prodSnd _ _) n).hom z)) :=
  rfl

/-- In degrees `≥ 1`, the homology of the global term is `H^{n}(G, A)`. -/
noncomputable def tateGlobalCohomologyIso (n : ℕ) :
    (tateGlobalComplex A Aᵣ).homology (n + 1) ≅ cohomology A (n + 1) :=
  @asIso _ _ _ _ (HomologicalComplex.homologyMap (prodFst _ _) (n + 1))
    (isIso_homologyMap_prodFst (cochains A) (degZeroComplex (ModuleCat.of k (∀ w, Aᵣ w)))
      (isZero_degZeroComplex_homology_succ _ n))

omit [∀ w, TopologicalSpace (F w)] [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)]
  [∀ w, IsSmoothRep (Aᵣ w)] in
theorem tateGlobalCohomologyIso_hom (n : ℕ) :
    (tateGlobalCohomologyIso A Aᵣ n).hom =
      HomologicalComplex.homologyMap (prodFst _ _) (n + 1) :=
  rfl

/-- In degree `0`, the homology of the global term is `H⁰(G, A) × ∏_w A_w`. -/
noncomputable def tateGlobalCohomologyZeroIso :
    (tateGlobalComplex A Aᵣ).homology 0 ≅ ModuleCat.of k (cohomology A 0 × ∀ w, Aᵣ w) :=
  prodHomologyIso _ _ 0 ≪≫
    ((LinearEquiv.refl k (cohomology A 0)).prodCongr
      (degZeroHomologyIso (ModuleCat.of k (∀ w, Aᵣ w))).toLinearEquiv).toModuleIso

omit [∀ w, TopologicalSpace (F w)] [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)]
  [∀ w, IsSmoothRep (Aᵣ w)] in
theorem tateGlobalCohomologyZeroIso_hom_apply (z : (tateGlobalComplex A Aᵣ).homology 0) :
    (tateGlobalCohomologyZeroIso A Aᵣ).hom.hom z =
      ((HomologicalComplex.homologyMap (prodFst _ _) 0).hom z,
        (degZeroHomologyIso (ModuleCat.of k (∀ w, Aᵣ w))).hom.hom
          ((HomologicalComplex.homologyMap (prodSnd _ _) 0).hom z)) :=
  rfl

theorem tateCompactRes_prodFst :
    tateCompactRes φ ψ A Aᵥ a Aᵣ ar ≫ prodFst _ _ = prodFst _ _ ≫ localRes φ A Aᵥ a :=
  prodLift_prodFst _ _

theorem tateCompactRes_prodSnd :
    tateCompactRes φ ψ A Aᵥ a Aᵣ ar ≫ prodSnd _ _ =
      prodFst _ _ ≫ localRes ψ A Aᵣ ar + prodSnd _ _ ≫ normCochains Aᵣ :=
  prodLift_prodSnd _ _

/-- Localization to all local groups, `Hⁿ(G, A) → ∏_v Hⁿ(H_v, A_v) × ∏_w Hⁿ(F_w, A_w)`. -/
noncomputable def tateGlobalToLocal (n : ℕ) :
    cohomology A n ⟶ ModuleCat.of k ((∀ v, cohomology (Aᵥ v) n) × (∀ w, cohomology (Aᵣ w) n)) :=
  ModuleCat.ofHom ((globalToLocal φ A Aᵥ a n).hom.prod (globalToLocal ψ A Aᵣ ar n).hom)

omit [∀ w, Fintype (F w)] in
theorem tateGlobalToLocal_hom_apply (n : ℕ) (x : cohomology A n) :
    (tateGlobalToLocal φ ψ A Aᵥ a Aᵣ ar n).hom x =
      ((globalToLocal φ A Aᵥ a n).hom x, (globalToLocal ψ A Aᵣ ar n).hom x) :=
  rfl

theorem homologyMap_tateCompactRes_succ (n : ℕ) :
    HomologicalComplex.homologyMap (tateCompactRes φ ψ A Aᵥ a Aᵣ ar) (n + 1) ≫
        (tateLocalCohomologyIso Aᵥ Aᵣ (n + 1)).hom =
      (tateGlobalCohomologyIso A Aᵣ n).hom ≫ tateGlobalToLocal φ ψ A Aᵥ a Aᵣ ar (n + 1) := by
  have e1 : HomologicalComplex.homologyMap (tateCompactRes φ ψ A Aᵥ a Aᵣ ar) (n + 1) ≫
      HomologicalComplex.homologyMap (prodFst _ _) (n + 1) ≫ (localCohomologyIso Aᵥ (n + 1)).hom =
      (tateGlobalCohomologyIso A Aᵣ n).hom ≫ globalToLocal φ A Aᵥ a (n + 1) := by
    rw [← HomologicalComplex.homologyMap_comp_assoc, tateCompactRes_prodFst,
      HomologicalComplex.homologyMap_comp_assoc, homologyMap_localRes_localCohomologyIso_hom]
    rfl
  have hz : HomologicalComplex.homologyMap
      (prodSnd (cochains A) (degZeroComplex (ModuleCat.of k (∀ w, Aᵣ w)))) (n + 1) = 0 :=
    (isZero_degZeroComplex_homology_succ _ n).eq_of_tgt _ _
  have e2 : HomologicalComplex.homologyMap (tateCompactRes φ ψ A Aᵥ a Aᵣ ar) (n + 1) ≫
      HomologicalComplex.homologyMap (prodSnd _ _) (n + 1) ≫ (localCohomologyIso Aᵣ (n + 1)).hom =
      (tateGlobalCohomologyIso A Aᵣ n).hom ≫ globalToLocal ψ A Aᵣ ar (n + 1) := by
    rw [← HomologicalComplex.homologyMap_comp_assoc, tateCompactRes_prodSnd,
      HomologicalComplex.homologyMap_add, HomologicalComplex.homologyMap_comp,
      HomologicalComplex.homologyMap_comp, hz, zero_comp, add_zero, Category.assoc,
      homologyMap_localRes_localCohomologyIso_hom]
    rfl
  refine ModuleCat.hom_ext (LinearMap.ext fun z => Prod.ext ?_ ?_)
  · exact hom_apply_hom_apply_of_comp_eq e1 z
  · exact hom_apply_hom_apply_of_comp_eq e2 z

end Terms

section Sequence

/-- The map `Ĥ_c^n(G, A) → Hⁿ(G, A)`. -/
noncomputable def tateToGlobal (n : ℕ) :
    tateCompactCohomology φ ψ A Aᵥ a Aᵣ ar n ⟶ cohomology A n :=
  HomologicalComplex.homologyMap
    (mappingCoconeNat.fst (tateCompactRes φ ψ A Aᵥ a Aᵣ ar) ≫ prodFst _ _) n

/-- The connecting map from the local cohomology to `Ĥ_c^{n+1}(G, A)`. -/
noncomputable def tateLocalToCompact (n : ℕ) :
    ModuleCat.of k ((∀ v, cohomology (Aᵥ v) n) × (∀ w, cohomology (Aᵣ w) n)) ⟶
      tateCompactCohomology φ ψ A Aᵥ a Aᵣ ar (n + 1) :=
  (tateLocalCohomologyIso Aᵥ Aᵣ n).inv ≫
    mappingCoconeNat.homologyδ (tateCompactRes φ ψ A Aᵥ a Aᵣ ar) n

theorem tateToGlobal_succ (n : ℕ) :
    tateToGlobal φ ψ A Aᵥ a Aᵣ ar (n + 1) =
      HomologicalComplex.homologyMap (mappingCoconeNat.fst (tateCompactRes φ ψ A Aᵥ a Aᵣ ar))
        (n + 1) ≫ (tateGlobalCohomologyIso A Aᵣ n).hom :=
  HomologicalComplex.homologyMap_comp _ _ _

@[reassoc (attr := simp)]
theorem tateToGlobal_tateGlobalToLocal (n : ℕ) :
    tateToGlobal φ ψ A Aᵥ a Aᵣ ar (n + 1) ≫ tateGlobalToLocal φ ψ A Aᵥ a Aᵣ ar (n + 1) = 0 := by
  refine (congrArg (· ≫ tateGlobalToLocal φ ψ A Aᵥ a Aᵣ ar (n + 1))
    (tateToGlobal_succ φ ψ A Aᵥ a Aᵣ ar n)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (homologyMap_tateCompactRes_succ φ ψ A Aᵥ a Aᵣ ar n).symm).trans ?_
  exact (mappingCoconeNat.homologyMap_fst_homologyMap_assoc _ _ _).trans zero_comp

@[reassoc (attr := simp)]
theorem tateGlobalToLocal_tateLocalToCompact (n : ℕ) :
    tateGlobalToLocal φ ψ A Aᵥ a Aᵣ ar (n + 1) ≫ tateLocalToCompact φ ψ A Aᵥ a Aᵣ ar (n + 1) = 0 := by
  rw [← cancel_epi (tateGlobalCohomologyIso A Aᵣ n).hom, comp_zero, ← Category.assoc,
    ← homologyMap_tateCompactRes_succ]
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Iso.hom_inv_id_assoc _ _)).trans
    (mappingCoconeNat.homologyMap_homologyδ _ _))

@[reassoc (attr := simp)]
theorem tateLocalToCompact_tateToGlobal (n : ℕ) :
    tateLocalToCompact φ ψ A Aᵥ a Aᵣ ar n ≫ tateToGlobal φ ψ A Aᵥ a Aᵣ ar (n + 1) = 0 := by
  refine (congrArg (tateLocalToCompact φ ψ A Aᵥ a Aᵣ ar n ≫ ·)
    (tateToGlobal_succ φ ψ A Aᵥ a Aᵣ ar n)).trans ?_
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (mappingCoconeNat.homologyδ_homologyMap_fst_assoc _ _ _)).trans (by rw [zero_comp, comp_zero]))

theorem tateCompactCohomology_exact_global (n : ℕ) :
    (ShortComplex.mk _ _ (tateToGlobal_tateGlobalToLocal φ ψ A Aᵥ a Aᵣ ar n)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (mappingCoconeNat.homology_exact₃ (tateCompactRes φ ψ A Aᵥ a Aᵣ ar) (n + 1))
  exact ShortComplex.isoMk (Iso.refl _) (tateGlobalCohomologyIso A Aᵣ n)
    (tateLocalCohomologyIso Aᵥ Aᵣ (n + 1))
    ((Category.id_comp _).trans (tateToGlobal_succ φ ψ A Aᵥ a Aᵣ ar n))
    (homologyMap_tateCompactRes_succ φ ψ A Aᵥ a Aᵣ ar n).symm

theorem tateCompactCohomology_exact_local (n : ℕ) :
    (ShortComplex.mk _ _ (tateGlobalToLocal_tateLocalToCompact φ ψ A Aᵥ a Aᵣ ar n)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (mappingCoconeNat.homology_exact₁ (tateCompactRes φ ψ A Aᵥ a Aᵣ ar) (n + 1))
  exact ShortComplex.isoMk (tateGlobalCohomologyIso A Aᵣ n) (tateLocalCohomologyIso Aᵥ Aᵣ (n + 1))
    (Iso.refl _) (homologyMap_tateCompactRes_succ φ ψ A Aᵥ a Aᵣ ar n).symm
    ((Iso.hom_inv_id_assoc _ _).trans (Category.comp_id _).symm)

theorem tateCompactCohomology_exact_compact (n : ℕ) :
    (ShortComplex.mk _ _ (tateLocalToCompact_tateToGlobal φ ψ A Aᵥ a Aᵣ ar n)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (mappingCoconeNat.homology_exact₂ (tateCompactRes φ ψ A Aᵥ a Aᵣ ar) n)
  exact ShortComplex.isoMk (tateLocalCohomologyIso Aᵥ Aᵣ n) (Iso.refl _)
    (tateGlobalCohomologyIso A Aᵣ n)
    ((Iso.hom_inv_id_assoc _ _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (tateToGlobal_succ φ ψ A Aᵥ a Aᵣ ar n))

end Sequence

section Zero

/-- The map `Ĥ_c^0(G, A) → H⁰(G, A) × ∏_w A_w`. -/
noncomputable def tateToGlobalZero :
    tateCompactCohomology φ ψ A Aᵥ a Aᵣ ar 0 ⟶ ModuleCat.of k (cohomology A 0 × ∀ w, Aᵣ w) :=
  HomologicalComplex.homologyMap (mappingCoconeNat.fst (tateCompactRes φ ψ A Aᵥ a Aᵣ ar)) 0 ≫
    (tateGlobalCohomologyZeroIso A Aᵣ).hom

/-- The degree-`0` localization map of the Tate-modified sequence. -/
noncomputable def tateGlobalZeroToLocal :
    ModuleCat.of k (cohomology A 0 × ∀ w, Aᵣ w) ⟶
      ModuleCat.of k ((∀ v, cohomology (Aᵥ v) 0) × (∀ w, cohomology (Aᵣ w) 0)) :=
  (tateGlobalCohomologyZeroIso A Aᵣ).inv ≫
    HomologicalComplex.homologyMap (tateCompactRes φ ψ A Aᵥ a Aᵣ ar) 0 ≫
      (tateLocalCohomologyIso Aᵥ Aᵣ 0).hom

@[reassoc (attr := simp)]
theorem tateToGlobalZero_tateGlobalZeroToLocal :
    tateToGlobalZero φ ψ A Aᵥ a Aᵣ ar ≫ tateGlobalZeroToLocal φ ψ A Aᵥ a Aᵣ ar = 0 := by
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Iso.hom_inv_id_assoc _ _)).trans
    ((mappingCoconeNat.homologyMap_fst_homologyMap_assoc _ 0 _).trans zero_comp))

@[reassoc (attr := simp)]
theorem tateGlobalZeroToLocal_tateLocalToCompact :
    tateGlobalZeroToLocal φ ψ A Aᵥ a Aᵣ ar ≫ tateLocalToCompact φ ψ A Aᵥ a Aᵣ ar 0 = 0 := by
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (Iso.hom_inv_id_assoc _ _)).trans
      (mappingCoconeNat.homologyMap_homologyδ _ 0)))).trans comp_zero)

theorem tateCompactCohomology_exact_localZero :
    (ShortComplex.mk _ _ (tateGlobalZeroToLocal_tateLocalToCompact φ ψ A Aᵥ a Aᵣ ar)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (mappingCoconeNat.homology_exact₁ (tateCompactRes φ ψ A Aᵥ a Aᵣ ar) 0)
  exact ShortComplex.isoMk (tateGlobalCohomologyZeroIso A Aᵣ) (tateLocalCohomologyIso Aᵥ Aᵣ 0)
    (Iso.refl _) (Iso.hom_inv_id_assoc _ _)
    ((Iso.hom_inv_id_assoc _ _).trans (Category.comp_id _).symm)

section NormClass

variable {F' : Type u} [Group F'] [TopologicalSpace F'] [IsTopologicalGroup F'] [Fintype F']

/-- The class of the norm `N_F m` in `H⁰(F, B)`. -/
noncomputable def normClass (B : Rep.{u} k F') [IsSmoothRep B] (m : B) : cohomology B 0 :=
  ((cochains B).homologyπ 0).hom ((cochains B).cyclesMk
    (zeroCochain B (B.ρ.norm m)) 1 (by simp) (d_zeroCochain_norm B m))

end NormClass

theorem localCohomologyIso_homologyMap_normCochains
    (y : (degZeroComplex (ModuleCat.of k (∀ w, Aᵣ w))).homology 0) :
    (localCohomologyIso Aᵣ 0).hom.hom ((HomologicalComplex.homologyMap (normCochains Aᵣ) 0).hom y) =
      fun w => normClass (Aᵣ w)
        ((show ∀ w, Aᵣ w from (degZeroHomologyIso (ModuleCat.of k (∀ w, Aᵣ w))).hom.hom y) w) := by
  obtain ⟨c, rfl⟩ := homologyπ_hom_surjective _ 0 y
  funext w
  rw [degZeroHomologyIso_hom_homologyπ, homologyMap_homologyπ_apply]
  change (HomologicalComplex.homologyMap (piProj _ w) 0).hom
      (((piComplex fun w => cochains (Aᵣ w)).homologyπ 0).hom
        ((HomologicalComplex.cyclesMap (normCochains Aᵣ) 0).hom c)) = _
  rw [homologyMap_homologyπ_apply]
  unfold normClass
  congr 1
  apply iCycles_hom_injective
  rw [iCycles_cyclesMap_apply, iCycles_cyclesMap_apply]
  exact ((cochains (Aᵣ w)).i_cyclesMk _ _ _ _).symm

theorem tateGlobalZeroToLocal_hom_apply (x : cohomology A 0) (e : ∀ w, Aᵣ w) :
    (tateGlobalZeroToLocal φ ψ A Aᵥ a Aᵣ ar).hom (x, e) =
      ((globalToLocal φ A Aᵥ a 0).hom x,
        (globalToLocal ψ A Aᵣ ar 0).hom x + fun w => normClass (Aᵣ w) (e w)) := by
  set z := (tateGlobalCohomologyZeroIso A Aᵣ).inv.hom (x, e) with hz
  have hze : (tateGlobalCohomologyZeroIso A Aᵣ).hom.hom z = (x, e) :=
    hom_apply_hom_apply_of_comp_eq (Iso.inv_hom_id (tateGlobalCohomologyZeroIso A Aᵣ))
      (show ModuleCat.of k (cohomology A 0 × ∀ w, Aᵣ w) from (x, e))
  have hx : (HomologicalComplex.homologyMap (prodFst _ _) 0).hom z = x := congrArg Prod.fst hze
  have he : (degZeroHomologyIso (ModuleCat.of k (∀ w, Aᵣ w))).hom.hom
      ((HomologicalComplex.homologyMap (prodSnd _ _) 0).hom z) = e := congrArg Prod.snd hze
  change (tateLocalCohomologyIso Aᵥ Aᵣ 0).hom.hom
    ((HomologicalComplex.homologyMap (tateCompactRes φ ψ A Aᵥ a Aᵣ ar) 0).hom z) = _
  rw [tateLocalCohomologyIso_hom_apply]
  refine Prod.ext ?_ ?_
  · have e1 : HomologicalComplex.homologyMap (tateCompactRes φ ψ A Aᵥ a Aᵣ ar) 0 ≫
        HomologicalComplex.homologyMap (prodFst _ _) 0 ≫ (localCohomologyIso Aᵥ 0).hom =
        HomologicalComplex.homologyMap (prodFst _ _) 0 ≫ globalToLocal φ A Aᵥ a 0 := by
      rw [← HomologicalComplex.homologyMap_comp_assoc, tateCompactRes_prodFst,
        HomologicalComplex.homologyMap_comp_assoc, homologyMap_localRes_localCohomologyIso_hom]
    rw [← hx]
    exact hom_apply_hom_apply_of_comp_eq e1 z
  · have e2 : HomologicalComplex.homologyMap (tateCompactRes φ ψ A Aᵥ a Aᵣ ar) 0 ≫
        HomologicalComplex.homologyMap (prodSnd _ _) 0 =
        HomologicalComplex.homologyMap (prodFst _ _) 0 ≫
            HomologicalComplex.homologyMap (localRes ψ A Aᵣ ar) 0 +
          HomologicalComplex.homologyMap (prodSnd _ _) 0 ≫
            HomologicalComplex.homologyMap (normCochains Aᵣ) 0 := by
      rw [← HomologicalComplex.homologyMap_comp, tateCompactRes_prodSnd,
        HomologicalComplex.homologyMap_add, HomologicalComplex.homologyMap_comp,
        HomologicalComplex.homologyMap_comp]
    change (localCohomologyIso Aᵣ 0).hom.hom
      ((HomologicalComplex.homologyMap (prodSnd _ _) 0).hom
        ((HomologicalComplex.homologyMap (tateCompactRes φ ψ A Aᵥ a Aᵣ ar) 0).hom z)) = _
    rw [hom_apply_hom_apply_of_comp_eq e2 z, ModuleCat.hom_add, LinearMap.add_apply, map_add]
    congr 1
    · rw [← hx]
      exact hom_apply_hom_apply_of_comp_eq
        (homologyMap_localRes_localCohomologyIso_hom ψ A Aᵣ ar 0) _
    · rw [← he]
      exact localCohomologyIso_homologyMap_normCochains Aᵣ _

end Zero

end Tate

end LocalCohomologyIsoHomologyMapNormCochains

-- from RealPlaces/ConeMap.lean
section ConeMap

open CategoryTheory Limits


section Complexes

variable {k : Type u} [CommRing k]

/-- The components of `degZeroMap`. -/
noncomputable def degZeroMapF {E E' : ModuleCat.{u} k} (f : E ⟶ E') :
    ∀ n, (degZeroComplex E).X n ⟶ (degZeroComplex E').X n
  | 0 => f
  | _ + 1 => 0

/-- A morphism of modules as a morphism of complexes concentrated in degree `0`. -/
noncomputable def degZeroMap {E E' : ModuleCat.{u} k} (f : E ⟶ E') :
    degZeroComplex E ⟶ degZeroComplex E' :=
  CochainComplex.ofHom (degZeroMapF f) fun n => by
    rw [degZeroComplex_d, degZeroComplex_d, comp_zero, zero_comp]

theorem degZeroMap_f_zero_apply {E E' : ModuleCat.{u} k} (f : E ⟶ E') (e : (degZeroComplex E).X 0) :
    ((degZeroMap f).f 0).hom e = f.hom e :=
  rfl

theorem degZeroMap_id (E : ModuleCat.{u} k) : degZeroMap (𝟙 E) = 𝟙 _ := by
  ext n : 1
  cases n with
  | zero => rfl
  | succ n => exact ModuleCat.hom_ext (LinearMap.ext fun _ => Subsingleton.elim _ _)

theorem degZeroMap_comp {E E' E'' : ModuleCat.{u} k} (f : E ⟶ E') (f' : E' ⟶ E'') :
    degZeroMap (f ≫ f') = degZeroMap f ≫ degZeroMap f' := by
  ext n : 1
  cases n with
  | zero => rfl
  | succ n => exact ModuleCat.hom_ext (LinearMap.ext fun _ => Subsingleton.elim _ _)

/-- A short complex of modules as a short complex of complexes concentrated in degree `0`. -/
noncomputable def degZeroShortComplex (S : ShortComplex (ModuleCat.{u} k)) :
    ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ) :=
  ShortComplex.mk (degZeroMap S.f) (degZeroMap S.g) (by rw [← degZeroMap_comp, S.zero]; ext n : 1; cases n <;> rfl)

theorem degZeroShortComplex_shortExact {S : ShortComplex (ModuleCat.{u} k)} (hS : S.ShortExact) :
    (degZeroShortComplex S).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => by
    cases n with
    | zero => exact hS
    | succ n =>
      have h0 : IsZero ((degZeroComplex S.X₂).X (n + 1)) := ModuleCat.isZero_of_subsingleton _
      exact { exact := ShortComplex.exact_of_isZero_X₂ _ h0
              mono_f := (ModuleCat.mono_iff_injective _).2 fun x y _ =>
                Subsingleton.elim (α := PUnit) x y
              epi_g := (ModuleCat.epi_iff_surjective _).2 fun y =>
                ⟨PUnit.unit, Subsingleton.elim (α := PUnit) _ y⟩ }

/-- The product of two short complexes of complexes. -/
noncomputable def prodShortComplex (S T : ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ)) :
    ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ) :=
  ShortComplex.mk (prodMapCx S.f T.f) (prodMapCx S.g T.g)
    (HomologicalComplex.hom_ext _ _ fun n => ModuleCat.hom_ext (LinearMap.ext fun x => Prod.ext
      (hom_apply_hom_apply_of_comp_eq (congrArg (·.f n) S.zero) x.1)
      (hom_apply_hom_apply_of_comp_eq (congrArg (·.f n) T.zero) x.2)))

theorem prodShortComplex_shortExact {S T : ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ)}
    (hS : S.ShortExact) (hT : T.ShortExact) : (prodShortComplex S T).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => by
    have h1 := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS n
    have h2 := (HomologicalComplex.shortExact_iff_degreewise_shortExact T).1 hT n
    refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
    · rw [ShortComplex.moduleCat_exact_iff]
      intro (x : S.X₂.X n × T.X₂.X n) hx
      have e1 := h1.exact
      have e2 := h2.exact
      rw [ShortComplex.moduleCat_exact_iff] at e1 e2
      obtain ⟨y1, hy1⟩ := e1 x.1 (congrArg Prod.fst hx)
      obtain ⟨y2, hy2⟩ := e2 x.2 (congrArg Prod.snd hx)
      exact ⟨(show (prodComplex S.X₁ T.X₁).X n from (y1, y2)), Prod.ext hy1 hy2⟩
    · exact (ModuleCat.mono_iff_injective _).2 fun (x x' : S.X₁.X n × T.X₁.X n) hxx =>
        Prod.ext ((ModuleCat.mono_iff_injective _).1 h1.mono_f (congrArg Prod.fst hxx))
          ((ModuleCat.mono_iff_injective _).1 h2.mono_f (congrArg Prod.snd hxx))
    · refine (ModuleCat.epi_iff_surjective _).2 fun (z : S.X₃.X n × T.X₃.X n) => ?_
      obtain ⟨y1, hy1⟩ := (ModuleCat.epi_iff_surjective _).1 h1.epi_g z.1
      obtain ⟨y2, hy2⟩ := (ModuleCat.epi_iff_surjective _).1 h2.epi_g z.2
      exact ⟨(show (prodComplex S.X₂ T.X₂).X n from (y1, y2)), Prod.ext hy1 hy2⟩

theorem homologyMap_prodMapCx_prodHomologyIso_hom {M N M' N' : CochainComplex (ModuleCat.{u} k) ℕ}
    (f : M ⟶ M') (g : N ⟶ N') (n : ℕ) :
    HomologicalComplex.homologyMap (prodMapCx f g) n ≫ (prodHomologyIso M' N' n).hom =
      (prodHomologyIso M N n).hom ≫ ModuleCat.ofHom
        ((HomologicalComplex.homologyMap f n).hom.prodMap (HomologicalComplex.homologyMap g n).hom) := by
  have e1 : prodMapCx f g ≫ prodFst M' N' = prodFst M N ≫ f := prodLift_prodFst _ _
  have e2 : prodMapCx f g ≫ prodSnd M' N' = prodSnd M N ≫ g := prodLift_prodSnd _ _
  refine ModuleCat.hom_ext (LinearMap.ext fun z => Prod.ext ?_ ?_)
  · exact hom_apply_hom_apply_eq_of_comp_eq (by
      rw [← HomologicalComplex.homologyMap_comp, e1, HomologicalComplex.homologyMap_comp]
      exact ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)) z
  · exact hom_apply_hom_apply_eq_of_comp_eq (by
      rw [← HomologicalComplex.homologyMap_comp, e2, HomologicalComplex.homologyMap_comp]
      exact ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)) z

end Complexes

section RepProducts

variable {k : Type u} [CommRing k] {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)]

/-- The product of a family of morphisms of representations, as a morphism of modules. -/
noncomputable def piRepHom {Aᵣ Bᵣ : ∀ w, Rep.{u} k (F w)} (g : ∀ w, Aᵣ w ⟶ Bᵣ w) :
    ModuleCat.of k (∀ w, Aᵣ w) ⟶ ModuleCat.of k (∀ w, Bᵣ w) :=
  ModuleCat.ofHom (LinearMap.pi fun w => (g w).hom.toLinearMap.comp (LinearMap.proj w))

theorem piRepHom_apply {Aᵣ Bᵣ : ∀ w, Rep.{u} k (F w)} (g : ∀ w, Aᵣ w ⟶ Bᵣ w)
    (e : ∀ w, Aᵣ w) (w : κ) : (piRepHom g).hom e w = (g w).hom (e w) :=
  rfl

/-- The product of a family of short complexes of representations, as a short complex of modules. -/
noncomputable def piRepShortComplex (S : ∀ w, ShortComplex (Rep.{u} k (F w))) :
    ShortComplex (ModuleCat.{u} k) :=
  ShortComplex.mk (piRepHom fun w => (S w).f) (piRepHom fun w => (S w).g)
    (ModuleCat.hom_ext (LinearMap.ext fun e => funext fun w =>
      congrArg (fun φ => Rep.Hom.hom φ (e w)) (S w).zero))

theorem piRepShortComplex_shortExact {S : ∀ w, ShortComplex (Rep.{u} k (F w))}
    (hS : ∀ w, (S w).ShortExact) : (piRepShortComplex S).ShortExact := by
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff]
    intro (x : ∀ w, (S w).X₂) hx
    have e : ∀ w, ∃ y : (S w).X₁, (S w).f.hom y = x w := fun w => by
      have ev := (hS w).exact.map (forget₂ (Rep.{u} k (F w)) (ModuleCat k))
      rw [ShortComplex.moduleCat_exact_iff] at ev
      exact ev (x w) (congrFun hx w)
    choose y hy using e
    exact ⟨show ∀ w, (S w).X₁ from y, funext hy⟩
  · exact (ModuleCat.mono_iff_injective _).2 fun (x x' : ∀ w, (S w).X₁) hxx => funext fun w =>
      (Rep.mono_iff_injective _).1 (hS w).mono_f (congrFun hxx w)
  · refine (ModuleCat.epi_iff_surjective _).2 fun (z : ∀ w, (S w).X₃) => ?_
    have e : ∀ w, ∃ y : (S w).X₂, (S w).g.hom y = z w := fun w =>
      (Rep.epi_iff_surjective _).1 (hS w).epi_g (z w)
    choose y hy using e
    exact ⟨show ∀ w, (S w).X₂ from y, funext hy⟩

end RepProducts

section Tate

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)

section Functoriality

variable {A B C : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B] [IsSmoothRep C]
  {Aᵥ Bᵥ Cᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsSmoothRep (Aᵥ v)] [∀ v, IsSmoothRep (Bᵥ v)]
  [∀ v, IsSmoothRep (Cᵥ v)] {a : ∀ v, Rep.res (φ v : H v →* G) A ⟶ Aᵥ v}
  {b : ∀ v, Rep.res (φ v : H v →* G) B ⟶ Bᵥ v} {c : ∀ v, Rep.res (φ v : H v →* G) C ⟶ Cᵥ v}
  {Aᵣ Bᵣ Cᵣ : ∀ w, Rep.{u} k (F w)} [∀ w, IsSmoothRep (Aᵣ w)] [∀ w, IsSmoothRep (Bᵣ w)]
  [∀ w, IsSmoothRep (Cᵣ w)] {ar : ∀ w, Rep.res (ψ w : F w →* G) A ⟶ Aᵣ w}
  {br : ∀ w, Rep.res (ψ w : F w →* G) B ⟶ Bᵣ w} {cr : ∀ w, Rep.res (ψ w : F w →* G) C ⟶ Cᵣ w}

omit [IsTopologicalGroup G] in

theorem normCochains_naturality (gᵣ : ∀ w, Aᵣ w ⟶ Bᵣ w) :
    normCochains Aᵣ ≫ piMap (fun w => coeffCochainsMap (gᵣ w)) =
      degZeroMap (piRepHom gᵣ) ≫ normCochains Bᵣ := by
  ext n : 1
  cases n with
  | zero =>
    refine ModuleCat.hom_ext (LinearMap.ext fun e => funext fun w => ?_)
    apply cochainOf_injective
    funext σ
    change (gᵣ w).hom ((Aᵣ w).ρ.norm (e w)) = (Bᵣ w).ρ.norm ((gᵣ w).hom (e w))
    exact (congrArg (fun f => Rep.Hom.hom f (e w)) (Rep.norm_comm (gᵣ w))).symm
  | succ n =>
    change (0 : _ ⟶ _) ≫ _ = _ ≫ (0 : _ ⟶ _)
    rw [zero_comp, comp_zero]

variable (g : A ⟶ B) (gᵥ : ∀ v, Aᵥ v ⟶ Bᵥ v) (gᵣ : ∀ w, Aᵣ w ⟶ Bᵣ w)
  (hg : ∀ v, a v ≫ gᵥ v = (Rep.resFunctor (φ v : H v →* G)).map g ≫ b v)
  (hgr : ∀ w, ar w ≫ gᵣ w = (Rep.resFunctor (ψ w : F w →* G)).map g ≫ br w)

/-- The map of global terms induced by compatible coefficient maps. -/
noncomputable abbrev tateGlobalMap : tateGlobalComplex A Aᵣ ⟶ tateGlobalComplex B Bᵣ :=
  prodMapCx (coeffCochainsMap g) (degZeroMap (piRepHom gᵣ))

/-- The map of local terms induced by compatible coefficient maps. -/
noncomputable abbrev tateLocalMap : tateLocalComplex Aᵥ Aᵣ ⟶ tateLocalComplex Bᵥ Bᵣ :=
  prodMapCx (piMap fun v => coeffCochainsMap (gᵥ v)) (piMap fun w => coeffCochainsMap (gᵣ w))

include hg hgr in

theorem tateCompactRes_naturality :
    tateCompactRes φ ψ A Aᵥ a Aᵣ ar ≫ tateLocalMap gᵥ gᵣ =
      tateGlobalMap g gᵣ ≫ tateCompactRes φ ψ B Bᵥ b Bᵣ br := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun x => Prod.ext ?_ ?_)
  · exact hom_apply_hom_apply_eq_of_comp_eq (congrArg (·.f n) (localRes_naturality φ g gᵥ hg)) x.1
  · change ((piMap fun w => coeffCochainsMap (gᵣ w)).f n).hom
        (((localRes ψ A Aᵣ ar).f n).hom x.1 + ((normCochains Aᵣ).f n).hom x.2) =
      ((localRes ψ B Bᵣ br).f n).hom (((coeffCochainsMap g).f n).hom x.1) +
        ((normCochains Bᵣ).f n).hom (((degZeroMap (piRepHom gᵣ)).f n).hom x.2)
    rw [map_add]
    exact congrArg₂ (· + ·)
      (hom_apply_hom_apply_eq_of_comp_eq (congrArg (·.f n) (localRes_naturality ψ g gᵣ hgr)) x.1)
      (hom_apply_hom_apply_eq_of_comp_eq (congrArg (·.f n) (normCochains_naturality gᵣ)) x.2)

/-- The map of Tate-modified compactly supported cochains induced by compatible coefficient maps. -/
noncomputable def tateCompactCochainsMap :
    tateCompactCochains φ ψ A Aᵥ a Aᵣ ar ⟶ tateCompactCochains φ ψ B Bᵥ b Bᵣ br :=
  mappingCoconeNat.map (tateGlobalMap g gᵣ) (tateLocalMap gᵥ gᵣ)
    (tateCompactRes_naturality φ ψ g gᵥ gᵣ hg hgr)

/-- The map `Ĥ_c^n(G, A) → Ĥ_c^n(G, B)` induced by compatible coefficient maps. -/
noncomputable def tateCompactCohomologyMap (n : ℕ) :
    tateCompactCohomology φ ψ A Aᵥ a Aᵣ ar n ⟶ tateCompactCohomology φ ψ B Bᵥ b Bᵣ br n :=
  HomologicalComplex.homologyMap (tateCompactCochainsMap φ ψ g gᵥ gᵣ hg hgr) n

omit [∀ v, IsSmoothRep (Bᵥ v)] [∀ v, IsSmoothRep (Cᵥ v)] [IsSmoothRep B] [IsSmoothRep C]
  [∀ w, IsSmoothRep (Bᵣ w)] [∀ w, IsSmoothRep (Cᵣ w)] in
@[simp]
theorem tateCompactCohomologyMap_id (n : ℕ) :
    tateCompactCohomologyMap φ ψ (𝟙 A) (fun v => 𝟙 (Aᵥ v)) (fun w => 𝟙 (Aᵣ w)) (a := a) (ar := ar)
      (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm)
      (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm) n = 𝟙 _ := by
  have h : tateCompactCochainsMap φ ψ (𝟙 A) (fun v => 𝟙 (Aᵥ v)) (fun w => 𝟙 (Aᵣ w)) (a := a)
      (ar := ar) (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm)
      (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm) = 𝟙 _ := by
    ext n : 1
    refine ModuleCat.hom_ext (LinearMap.ext fun (p : (tateGlobalComplex A Aᵣ).X n ×
      shiftNegOneX (tateLocalComplex Aᵥ Aᵣ) n) => Prod.ext (Prod.ext rfl ?_) ?_)
    · cases n with
      | zero => rfl
      | succ n => exact Subsingleton.elim _ _
    · cases n with
      | zero => rfl
      | succ n => rfl
  exact (congrArg (HomologicalComplex.homologyMap · n) h).trans
    (HomologicalComplex.homologyMap_id _ n)

theorem tateCompactCohomologyMap_comp (g' : B ⟶ C) (gᵥ' : ∀ v, Bᵥ v ⟶ Cᵥ v)
    (gᵣ' : ∀ w, Bᵣ w ⟶ Cᵣ w)
    (hg' : ∀ v, b v ≫ gᵥ' v = (Rep.resFunctor (φ v : H v →* G)).map g' ≫ c v)
    (hgr' : ∀ w, br w ≫ gᵣ' w = (Rep.resFunctor (ψ w : F w →* G)).map g' ≫ cr w) (n : ℕ) :
    tateCompactCohomologyMap φ ψ (g ≫ g') (fun v => gᵥ v ≫ gᵥ' v) (fun w => gᵣ w ≫ gᵣ' w)
        (fun v => by rw [reassoc_of% hg v, hg' v, Functor.map_comp, Category.assoc])
        (fun w => by rw [reassoc_of% hgr w, hgr' w, Functor.map_comp, Category.assoc]) n =
      tateCompactCohomologyMap φ ψ g gᵥ gᵣ hg hgr n ≫
        tateCompactCohomologyMap φ ψ g' gᵥ' gᵣ' hg' hgr' n := by
  have h : tateCompactCochainsMap φ ψ (g ≫ g') (fun v => gᵥ v ≫ gᵥ' v) (fun w => gᵣ w ≫ gᵣ' w)
      (fun v => by rw [reassoc_of% hg v, hg' v, Functor.map_comp, Category.assoc])
      (fun w => by rw [reassoc_of% hgr w, hgr' w, Functor.map_comp, Category.assoc]) =
      tateCompactCochainsMap φ ψ g gᵥ gᵣ hg hgr ≫ tateCompactCochainsMap φ ψ g' gᵥ' gᵣ' hg' hgr' := by
    ext n : 1
    refine ModuleCat.hom_ext (LinearMap.ext fun (p : (tateGlobalComplex A Aᵣ).X n ×
      shiftNegOneX (tateLocalComplex Aᵥ Aᵣ) n) => Prod.ext (Prod.ext rfl ?_) ?_)
    · cases n with
      | zero => rfl
      | succ n => exact Subsingleton.elim _ _
    · cases n with
      | zero => rfl
      | succ n => rfl
  exact (congrArg (HomologicalComplex.homologyMap · n) h).trans
    (HomologicalComplex.homologyMap_comp _ _ n)

theorem tateCompactCohomologyMap_tateToGlobal (n : ℕ) :
    tateCompactCohomologyMap φ ψ g gᵥ gᵣ hg hgr n ≫ tateToGlobal φ ψ B Bᵥ b Bᵣ br n =
      tateToGlobal φ ψ A Aᵥ a Aᵣ ar n ≫ coeffMap g n := by
  have e : tateCompactCochainsMap φ ψ g gᵥ gᵣ hg hgr ≫
      (mappingCoconeNat.fst (tateCompactRes φ ψ B Bᵥ b Bᵣ br) ≫ prodFst _ _) =
      (mappingCoconeNat.fst (tateCompactRes φ ψ A Aᵥ a Aᵣ ar) ≫ prodFst _ _) ≫ coeffCochainsMap g :=
    HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)
  exact (HomologicalComplex.homologyMap_comp _ _ _).symm.trans
    ((congrArg (HomologicalComplex.homologyMap · n) e).trans
      (HomologicalComplex.homologyMap_comp _ _ _))

omit [∀ w, Fintype (F w)] in
include hg hgr in

theorem cohomologyMap_tateGlobalToLocal (n : ℕ) :
    coeffMap g n ≫ tateGlobalToLocal φ ψ B Bᵥ b Bᵣ br n =
      tateGlobalToLocal φ ψ A Aᵥ a Aᵣ ar n ≫ ModuleCat.ofHom
        ((LinearMap.pi fun v => (coeffMap (gᵥ v) n).hom.comp (LinearMap.proj v)).prodMap
          (LinearMap.pi fun w => (coeffMap (gᵣ w) n).hom.comp (LinearMap.proj w))) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => Prod.ext ?_ ?_)
  · exact hom_apply_hom_apply_eq_of_comp_eq (cohomologyMap_globalToLocal φ g gᵥ hg n) x
  · exact hom_apply_hom_apply_eq_of_comp_eq (cohomologyMap_globalToLocal ψ g gᵣ hgr n) x

omit [∀ w, Fintype (F w)] in

theorem homologyMap_tateLocalMap_tateLocalCohomologyIso_hom (n : ℕ) :
    HomologicalComplex.homologyMap (tateLocalMap gᵥ gᵣ) n ≫ (tateLocalCohomologyIso Bᵥ Bᵣ n).hom =
      (tateLocalCohomologyIso Aᵥ Aᵣ n).hom ≫ ModuleCat.ofHom
        ((LinearMap.pi fun v => (coeffMap (gᵥ v) n).hom.comp (LinearMap.proj v)).prodMap
          (LinearMap.pi fun w => (coeffMap (gᵣ w) n).hom.comp (LinearMap.proj w))) := by
  have e1 := homologyMap_prodMapCx_prodHomologyIso_hom (piMap fun v => coeffCochainsMap (gᵥ v))
    (piMap fun w => coeffCochainsMap (gᵣ w)) n
  have e2 := homologyMap_piMap_piHomologyIso_hom (fun v => coeffCochainsMap (gᵥ v)) n
  have e3 := homologyMap_piMap_piHomologyIso_hom (fun w => coeffCochainsMap (gᵣ w)) n
  refine ModuleCat.hom_ext (LinearMap.ext fun z => Prod.ext ?_ ?_)
  · have h1 := congrArg Prod.fst (hom_apply_hom_apply_eq_of_comp_eq e1 z)
    change (localCohomologyIso Bᵥ n).hom.hom (HomologicalComplex.homologyMap (prodFst _ _) n |>.hom
        ((HomologicalComplex.homologyMap (tateLocalMap gᵥ gᵣ) n).hom z)) = _
    rw [show (HomologicalComplex.homologyMap (prodFst _ _) n).hom
        ((HomologicalComplex.homologyMap (tateLocalMap gᵥ gᵣ) n).hom z) = _ from h1]
    exact hom_apply_hom_apply_eq_of_comp_eq e2 _
  · have h2 := congrArg Prod.snd (hom_apply_hom_apply_eq_of_comp_eq e1 z)
    change (localCohomologyIso Bᵣ n).hom.hom (HomologicalComplex.homologyMap (prodSnd _ _) n |>.hom
        ((HomologicalComplex.homologyMap (tateLocalMap gᵥ gᵣ) n).hom z)) = _
    rw [show (HomologicalComplex.homologyMap (prodSnd _ _) n).hom
        ((HomologicalComplex.homologyMap (tateLocalMap gᵥ gᵣ) n).hom z) = _ from h2]
    exact hom_apply_hom_apply_eq_of_comp_eq e3 _

theorem tateLocalToCompact_tateCompactCohomologyMap (n : ℕ) :
    tateLocalToCompact φ ψ A Aᵥ a Aᵣ ar n ≫ tateCompactCohomologyMap φ ψ g gᵥ gᵣ hg hgr (n + 1) =
      ModuleCat.ofHom
          ((LinearMap.pi fun v => (coeffMap (gᵥ v) n).hom.comp (LinearMap.proj v)).prodMap
            (LinearMap.pi fun w => (coeffMap (gᵣ w) n).hom.comp (LinearMap.proj w))) ≫
        tateLocalToCompact φ ψ B Bᵥ b Bᵣ br n := by
  have h2 : (tateLocalCohomologyIso Aᵥ Aᵣ n).inv ≫
      HomologicalComplex.homologyMap (tateLocalMap gᵥ gᵣ) n =
      ModuleCat.ofHom
          ((LinearMap.pi fun v => (coeffMap (gᵥ v) n).hom.comp (LinearMap.proj v)).prodMap
            (LinearMap.pi fun w => (coeffMap (gᵣ w) n).hom.comp (LinearMap.proj w))) ≫
        (tateLocalCohomologyIso Bᵥ Bᵣ n).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact homologyMap_tateLocalMap_tateLocalCohomologyIso_hom gᵥ gᵣ n
  have h := congrArg ((tateLocalCohomologyIso Aᵥ Aᵣ n).inv ≫ ·)
    (mappingCoconeNat.homologyδ_naturality (tateGlobalMap g gᵣ) (tateLocalMap gᵥ gᵣ)
      (tateCompactRes_naturality φ ψ g gᵥ gᵣ hg hgr) n)
  simp only [← Category.assoc] at h
  rw [h2, Category.assoc] at h
  exact h

end Functoriality

section CoefficientSequence

variable (S : ShortComplex (Rep.{u} k G)) [IsSmoothRep S.X₁] [IsSmoothRep S.X₂]
  [IsSmoothRep S.X₃] (Sᵥ : ∀ v, ShortComplex (Rep.{u} k (H v))) [∀ v, IsSmoothRep (Sᵥ v).X₁]
  [∀ v, IsSmoothRep (Sᵥ v).X₂] [∀ v, IsSmoothRep (Sᵥ v).X₃]
  (s : ∀ v, S.map (Rep.resFunctor (φ v : H v →* G)) ⟶ Sᵥ v)
  (Sᵣ : ∀ w, ShortComplex (Rep.{u} k (F w))) [∀ w, IsSmoothRep (Sᵣ w).X₁]
  [∀ w, IsSmoothRep (Sᵣ w).X₂] [∀ w, IsSmoothRep (Sᵣ w).X₃]
  (sr : ∀ w, S.map (Rep.resFunctor (ψ w : F w →* G)) ⟶ Sᵣ w)

/-- The short complex of global terms of a short complex of coefficients. -/
noncomputable abbrev tateGlobalShortComplex : ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ) :=
  prodShortComplex (cochainsShortComplex S) (degZeroShortComplex (piRepShortComplex Sᵣ))

/-- The short complex of local terms of short complexes of local coefficients. -/
noncomputable abbrev tateLocalShortComplex : ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ) :=
  prodShortComplex (piShortComplex fun v => cochainsShortComplex (Sᵥ v))
    (piShortComplex fun w => cochainsShortComplex (Sᵣ w))

/-- `tateCompactRes` for the three terms of a short complex of coefficients. -/
noncomputable def tateResShortComplex : tateGlobalShortComplex S Sᵣ ⟶ tateLocalShortComplex Sᵥ Sᵣ where
  τ₁ := tateCompactRes φ ψ S.X₁ (fun v => (Sᵥ v).X₁) (fun v => (s v).τ₁) (fun w => (Sᵣ w).X₁)
    (fun w => (sr w).τ₁)
  τ₂ := tateCompactRes φ ψ S.X₂ (fun v => (Sᵥ v).X₂) (fun v => (s v).τ₂) (fun w => (Sᵣ w).X₂)
    (fun w => (sr w).τ₂)
  τ₃ := tateCompactRes φ ψ S.X₃ (fun v => (Sᵥ v).X₃) (fun v => (s v).τ₃) (fun w => (Sᵣ w).X₃)
    (fun w => (sr w).τ₃)
  comm₁₂ := tateCompactRes_naturality φ ψ S.f (fun v => (Sᵥ v).f) (fun w => (Sᵣ w).f)
    (fun v => (s v).comm₁₂) (fun w => (sr w).comm₁₂)
  comm₂₃ := tateCompactRes_naturality φ ψ S.g (fun v => (Sᵥ v).g) (fun w => (Sᵣ w).g)
    (fun v => (s v).comm₂₃) (fun w => (sr w).comm₂₃)

/-- The first map of the short complex of Tate-modified cochains. -/
noncomputable abbrev tateCompactCochainsMap₁₂ :=
  tateCompactCochainsMap φ ψ (A := S.X₁) (B := S.X₂) (Aᵥ := fun v => (Sᵥ v).X₁)
      (Bᵥ := fun v => (Sᵥ v).X₂) (a := fun v => (s v).τ₁) (b := fun v => (s v).τ₂)
      (Aᵣ := fun w => (Sᵣ w).X₁) (Bᵣ := fun w => (Sᵣ w).X₂) (ar := fun w => (sr w).τ₁)
      (br := fun w => (sr w).τ₂)
    S.f (fun v => (Sᵥ v).f) (fun w => (Sᵣ w).f) (fun v => (s v).comm₁₂) (fun w => (sr w).comm₁₂)

/-- The second map of the short complex of Tate-modified cochains. -/
noncomputable abbrev tateCompactCochainsMap₂₃ :=
  tateCompactCochainsMap φ ψ (A := S.X₂) (B := S.X₃) (Aᵥ := fun v => (Sᵥ v).X₂)
      (Bᵥ := fun v => (Sᵥ v).X₃) (a := fun v => (s v).τ₂) (b := fun v => (s v).τ₃)
      (Aᵣ := fun w => (Sᵣ w).X₂) (Bᵣ := fun w => (Sᵣ w).X₃) (ar := fun w => (sr w).τ₂)
      (br := fun w => (sr w).τ₃)
    S.g (fun v => (Sᵥ v).g) (fun w => (Sᵣ w).g) (fun v => (s v).comm₂₃) (fun w => (sr w).comm₂₃)

/-- The first map of the long exact sequence of `Ĥ_c`. -/
noncomputable abbrev tateCompactCohomologyMap₁₂ (n : ℕ) :=
  tateCompactCohomologyMap φ ψ (A := S.X₁) (B := S.X₂) (Aᵥ := fun v => (Sᵥ v).X₁)
      (Bᵥ := fun v => (Sᵥ v).X₂) (a := fun v => (s v).τ₁) (b := fun v => (s v).τ₂)
      (Aᵣ := fun w => (Sᵣ w).X₁) (Bᵣ := fun w => (Sᵣ w).X₂) (ar := fun w => (sr w).τ₁)
      (br := fun w => (sr w).τ₂)
    S.f (fun v => (Sᵥ v).f) (fun w => (Sᵣ w).f) (fun v => (s v).comm₁₂) (fun w => (sr w).comm₁₂) n

/-- The second map of the long exact sequence of `Ĥ_c`. -/
noncomputable abbrev tateCompactCohomologyMap₂₃ (n : ℕ) :=
  tateCompactCohomologyMap φ ψ (A := S.X₂) (B := S.X₃) (Aᵥ := fun v => (Sᵥ v).X₂)
      (Bᵥ := fun v => (Sᵥ v).X₃) (a := fun v => (s v).τ₂) (b := fun v => (s v).τ₃)
      (Aᵣ := fun w => (Sᵣ w).X₂) (Bᵣ := fun w => (Sᵣ w).X₃) (ar := fun w => (sr w).τ₂)
      (br := fun w => (sr w).τ₃)
    S.g (fun v => (Sᵥ v).g) (fun w => (Sᵣ w).g) (fun v => (s v).comm₂₃) (fun w => (sr w).comm₂₃) n

theorem tateCompactCochainsMap₁₂_₂₃ :
    tateCompactCochainsMap₁₂ φ ψ S Sᵥ s Sᵣ sr ≫ tateCompactCochainsMap₂₃ φ ψ S Sᵥ s Sᵣ sr = 0 := by
  have hK := (tateGlobalShortComplex S Sᵣ).zero
  have hL := (tateLocalShortComplex Sᵥ Sᵣ).zero
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : (tateGlobalComplex S.X₁ fun w => (Sᵣ w).X₁).X n ×
    shiftNegOneX (tateLocalComplex (fun v => (Sᵥ v).X₁) fun w => (Sᵣ w).X₁) n) => Prod.ext ?_ ?_)
  · exact hom_apply_hom_apply_of_comp_eq (congrArg (·.f n) hK) p.1
  · cases n with
    | zero => rfl
    | succ n => exact hom_apply_hom_apply_of_comp_eq (congrArg (·.f n) hL) p.2

theorem tateCompactCohomologyMap_f_g (n : ℕ) :
    tateCompactCohomologyMap₁₂ φ ψ S Sᵥ s Sᵣ sr n ≫ tateCompactCohomologyMap₂₃ φ ψ S Sᵥ s Sᵣ sr n = 0 :=
  (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    ((congrArg (HomologicalComplex.homologyMap · n)
      (tateCompactCochainsMap₁₂_₂₃ φ ψ S Sᵥ s Sᵣ sr)).trans
      (HomologicalComplex.homologyMap_zero _ _ n))

theorem mapShortComplex_tateResShortComplex_f :
    (mappingCoconeNat.mapShortComplex (tateResShortComplex φ ψ S Sᵥ s Sᵣ sr)).f =
      tateCompactCochainsMap₁₂ φ ψ S Sᵥ s Sᵣ sr := by
  ext n : 1
  exact ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

theorem mapShortComplex_tateResShortComplex_g :
    (mappingCoconeNat.mapShortComplex (tateResShortComplex φ ψ S Sᵥ s Sᵣ sr)).g =
      tateCompactCochainsMap₂₃ φ ψ S Sᵥ s Sᵣ sr := by
  ext n : 1
  exact ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

variable {S Sᵥ Sᵣ}

theorem tateCompactCochains_shortExact (hS : S.ShortExact) (hSᵥ : ∀ v, (Sᵥ v).ShortExact)
    (hSᵣ : ∀ w, (Sᵣ w).ShortExact) :
    (mappingCoconeNat.mapShortComplex (tateResShortComplex φ ψ S Sᵥ s Sᵣ sr)).ShortExact :=
  mappingCoconeNat.shortExact_mapShortComplex _
    (prodShortComplex_shortExact (cochainsShortComplex_shortExact hS)
      (degZeroShortComplex_shortExact (piRepShortComplex_shortExact hSᵣ)))
    (prodShortComplex_shortExact
      (piShortComplex_shortExact fun v => cochainsShortComplex_shortExact (hSᵥ v))
      (piShortComplex_shortExact fun w => cochainsShortComplex_shortExact (hSᵣ w)))

/-- The connecting map `Ĥ_c^n(G, A₃) → Ĥ_c^{n+1}(G, A₁)` of a short exact sequence of
coefficients. -/
noncomputable def tateCompactδ (hS : S.ShortExact) (hSᵥ : ∀ v, (Sᵥ v).ShortExact)
    (hSᵣ : ∀ w, (Sᵣ w).ShortExact) (n : ℕ) :
    tateCompactCohomology φ ψ S.X₃ (fun v => (Sᵥ v).X₃) (fun v => (s v).τ₃) (fun w => (Sᵣ w).X₃)
        (fun w => (sr w).τ₃) n ⟶
      tateCompactCohomology φ ψ S.X₁ (fun v => (Sᵥ v).X₁) (fun v => (s v).τ₁)
        (fun w => (Sᵣ w).X₁) (fun w => (sr w).τ₁) (n + 1) :=
  (tateCompactCochains_shortExact φ ψ s sr hS hSᵥ hSᵣ).δ n (n + 1) rfl

variable (hS : S.ShortExact) (hSᵥ : ∀ v, (Sᵥ v).ShortExact) (hSᵣ : ∀ w, (Sᵣ w).ShortExact)

theorem tateCompactCohomologyMap₂₃_tateCompactδ (n : ℕ) :
    tateCompactCohomologyMap₂₃ φ ψ S Sᵥ s Sᵣ sr n ≫ tateCompactδ φ ψ s sr hS hSᵥ hSᵣ n = 0 := by
  have h := (tateCompactCochains_shortExact φ ψ s sr hS hSᵥ hSᵣ).comp_δ n (n + 1) rfl
  rw [mapShortComplex_tateResShortComplex_g] at h
  exact h

theorem tateCompactδ_tateCompactCohomologyMap₁₂ (n : ℕ) :
    tateCompactδ φ ψ s sr hS hSᵥ hSᵣ n ≫ tateCompactCohomologyMap₁₂ φ ψ S Sᵥ s Sᵣ sr (n + 1) = 0 := by
  have h := (tateCompactCochains_shortExact φ ψ s sr hS hSᵥ hSᵣ).δ_comp n (n + 1) rfl
  rw [mapShortComplex_tateResShortComplex_f] at h
  exact h

include hS hSᵥ hSᵣ in

theorem tateCompactCohomology_exact₂ (n : ℕ) :
    (ShortComplex.mk _ _ (tateCompactCohomologyMap_f_g φ ψ S Sᵥ s Sᵣ sr n)).Exact := by
  have h := (tateCompactCochains_shortExact φ ψ s sr hS hSᵥ hSᵣ).homology_exact₂ n
  refine (ShortComplex.exact_iff_of_iso ?_).1 h
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans ((congrArg (HomologicalComplex.homologyMap · _)
      (mapShortComplex_tateResShortComplex_f φ ψ S Sᵥ s Sᵣ sr)).symm.trans (Category.comp_id _).symm))
    ((Category.id_comp _).trans ((congrArg (HomologicalComplex.homologyMap · _)
      (mapShortComplex_tateResShortComplex_g φ ψ S Sᵥ s Sᵣ sr)).symm.trans (Category.comp_id _).symm))

theorem tateCompactCohomology_exact₃ (n : ℕ) :
    (ShortComplex.mk _ _ (tateCompactCohomologyMap₂₃_tateCompactδ φ ψ s sr hS hSᵥ hSᵣ n)).Exact := by
  have h := (tateCompactCochains_shortExact φ ψ s sr hS hSᵥ hSᵣ).homology_exact₃ n (n + 1) rfl
  refine (ShortComplex.exact_iff_of_iso ?_).1 h
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans ((congrArg (HomologicalComplex.homologyMap · _)
      (mapShortComplex_tateResShortComplex_g φ ψ S Sᵥ s Sᵣ sr)).symm.trans (Category.comp_id _).symm))
    ((Category.id_comp _).trans (Category.comp_id _).symm)

theorem tateCompactCohomology_exact₁ (n : ℕ) :
    (ShortComplex.mk _ _ (tateCompactδ_tateCompactCohomologyMap₁₂ φ ψ s sr hS hSᵥ hSᵣ n)).Exact := by
  have h := (tateCompactCochains_shortExact φ ψ s sr hS hSᵥ hSᵣ).homology_exact₁ n (n + 1) rfl
  refine (ShortComplex.exact_iff_of_iso ?_).1 h
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans ((congrArg (HomologicalComplex.homologyMap · _)
      (mapShortComplex_tateResShortComplex_f φ ψ S Sᵥ s Sᵣ sr)).symm.trans (Category.comp_id _).symm))

end CoefficientSequence

end Tate

end ConeMap

end Langlands.GaloisCohomology
