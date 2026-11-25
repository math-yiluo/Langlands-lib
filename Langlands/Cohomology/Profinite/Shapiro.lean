import Langlands.Cohomology.Profinite.Coinduced.Quotient
import Mathlib.RepresentationTheory.Coinduced

namespace Langlands.ProfiniteCohomology

open CategoryTheory Topology

universe u

variable {k G : Type u} [CommRing k] [Group G]

section Maps

variable (U : Subgroup G)

noncomputable def coindEvalOne (B : Rep.{u} k U) :
    Rep.res U.subtype (Rep.coind U.subtype B) ⟶ B :=
  Rep.ofHom ⟨(LinearMap.proj (1 : G)).comp (Representation.coindV U.subtype B.ρ).subtype,
    fun u => by
      ext f
      change f.1 (1 * (u : G)) = B.ρ u (f.1 1)
      rw [one_mul]
      simpa using f.2 u 1⟩

@[simp]
theorem coindEvalOne_hom_apply (B : Rep.{u} k U) (f : Rep.coind U.subtype B) :
    (coindEvalOne U B).hom f = f.1 1 :=
  rfl

noncomputable def coindUnit (A : Rep.{u} k G) :
    A ⟶ Rep.coind U.subtype (Rep.res U.subtype A) :=
  Rep.resCoindToHom U.subtype A (Rep.res U.subtype A) (𝟙 _)

@[simp]
theorem coindUnit_hom_apply (A : Rep.{u} k G) (a : A) (x : G) :
    ((coindUnit U A).hom a).1 x = A.ρ x a :=
  rfl

theorem coindUnit_comp_coindEvalOne (A : Rep.{u} k G) :
    (Rep.resFunctor U.subtype).map (coindUnit U A) ≫ coindEvalOne U (Rep.res U.subtype A) =
      𝟙 _ := by
  ext a
  change A.ρ 1 a = a
  simp


end Maps

variable [TopologicalSpace G] [IsTopologicalGroup G]

section Discrete

variable (U : OpenSubgroup G) (B : Rep.{u} k (U : Subgroup G)) [IsSmoothRep B]

theorem isLocallyConstant_coind (f : Rep.coind (U : Subgroup G).subtype B) :
    IsLocallyConstant (f.1 : G → B) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  set S : Set G := Subtype.val '' (vectorStabilizer B.ρ (f.1 x) : Set (U : Subgroup G))
  have hS : IsOpen S :=
    IsOpen.isOpenMap_subtype_val (s := (U : Set G)) U.isOpen _ (IsSmoothRep.isOpen_stabilizer B (f.1 x))
  have h1 : S ∈ 𝓝 (1 : G) := hS.mem_nhds ⟨1, (vectorStabilizer B.ρ (f.1 x)).one_mem, rfl⟩
  have hc : Continuous fun y : G => y * x⁻¹ := continuous_id.mul continuous_const
  have h2 : ∀ᶠ y in 𝓝 x, y * x⁻¹ ∈ S := hc.continuousAt.preimage_mem_nhds (by simpa using h1)
  filter_upwards [h2] with y hy
  obtain ⟨u, hu, huy⟩ := hy
  have hy' : y = (U : Subgroup G).subtype u * x := by
    simp only [Subgroup.subtype_apply, huy, inv_mul_cancel_right]
  rw [hy', f.2 u x]
  exact (mem_vectorStabilizer _ _ _).1 hu

noncomputable def coindToLocallyConstant (f : Rep.coind (U : Subgroup G).subtype B) :
    LocallyConstant G B :=
  ⟨f.1, isLocallyConstant_coind U B f⟩

instance isSmoothRep_coind [CompactSpace G] :
    IsSmoothRep (Rep.coind (U : Subgroup G).subtype B) :=
  IsSmoothRep.of_isOpen_stabilizer _ fun f => Subgroup.isOpen_of_mem_nhds (g := 1) _ <|
    Filter.mem_of_superset (eventually_forall_mul_eq (coindToLocallyConstant U B f))
      fun g (hg : ∀ x, f.1 (x * g) = f.1 x) => Subtype.ext (funext fun x => hg x)

instance finiteIndex_openSubgroup [CompactSpace G] (U : OpenSubgroup G) :
    (U : Subgroup G).FiniteIndex :=
  Subgroup.finiteIndex_of_finite_quotient

instance compactSpace_openSubgroup [CompactSpace G] (U : OpenSubgroup G) :
    CompactSpace (U : Subgroup G) :=
  isCompact_iff_compactSpace.mp (U.isClosed.isCompact)

end Discrete

section Shapiro

variable [CompactSpace G] (U : OpenSubgroup G) (B : Rep.{u} k (U : Subgroup G)) [IsSmoothRep B]

noncomputable def shapiroMap (n : ℕ) :
    cohomology (Rep.coind (U : Subgroup G).subtype B) n ⟶ cohomology B n :=
  map (subgroupInclusion (U : Subgroup G))
    (coindEvalOne (U : Subgroup G) B) n

theorem shapiroMap_eq (n : ℕ) :
    shapiroMap U B n = map (subgroupInclusion (U : Subgroup G)) (coindEvalOne (U : Subgroup G) B) n :=
  rfl

end Shapiro

end Langlands.ProfiniteCohomology

namespace Langlands.ProfiniteCohomology

open CategoryTheory Limits Topology

universe u

variable {k G : Type u} [CommRing k] [Group G]

section Exact

variable (U : Subgroup G)

noncomputable abbrev coindShortComplexOf (X : ShortComplex (Rep.{u} k U)) : ShortComplex (Rep.{u} k G) :=
  ShortComplex.mk (Rep.coindMap U.subtype X.f) (Rep.coindMap U.subtype X.g) (by
    ext F x
    exact congrArg (fun φ => φ.hom (F.1 x)) X.zero)

theorem shortExact_coindShortComplexOf {X : ShortComplex (Rep.{u} k U)} (hX : X.ShortExact) :
    (coindShortComplexOf U X).ShortExact := by
  have hf : Function.Injective X.f.hom := (Rep.mono_iff_injective _).1 hX.mono_f
  have hexact := hX.exact.map (forget₂ (Rep.{u} k U) (ModuleCat.{u} k))
  rw [ShortComplex.moduleCat_exact_iff] at hexact
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{u} k G) (ModuleCat.{u} k)),
      ShortComplex.moduleCat_exact_iff]
    intro F₀ hF₀
    let F : Rep.coind U.subtype X.X₂ := F₀
    have hF : ∀ x, X.g.hom (F.1 x) = 0 := fun x =>
      congrArg (fun φ : Rep.coind U.subtype X.X₃ => φ.1 x) hF₀
    have hy : ∀ x, ∃ y, X.f.hom y = F.1 x := fun x => hexact (F.1 x) (hF x)
    choose y hy using hy
    refine ⟨(⟨y, fun u x => hf ?_⟩ : Rep.coind U.subtype X.X₁), Subtype.ext (funext hy)⟩
    rw [hy, F.2 u x, ← hy x]
    exact (Rep.hom_comm_apply X.f u (y x)).symm
  · refine (Rep.mono_iff_injective _).2 fun a b h => Subtype.ext (funext fun x => hf ?_)
    exact congrArg (fun φ : Rep.coind U.subtype X.X₂ => φ.1 x) h
  · have := hX.epi_g
    exact (Rep.coindFunctor k U.subtype).map_epi X.g

noncomputable def coindEvalOneShortComplex (X : ShortComplex (Rep.{u} k U)) :
    (coindShortComplexOf U X).map (Rep.resFunctor U.subtype) ⟶ X where
  τ₁ := coindEvalOne U X.X₁
  τ₂ := coindEvalOne U X.X₂
  τ₃ := coindEvalOne U X.X₃
  comm₁₂ := by
    ext f
    rfl
  comm₂₃ := by
    ext f
    rfl

end Exact

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (U : OpenSubgroup G)

section Naturality

set_option backward.isDefEq.respectTransparency false in
-- Coefficient maps are used at the definitionally equal types `Rep.res (.id _) B ⟶ B'`.
@[reassoc]
theorem shapiroMap_naturality {B B' : Rep.{u} k (U : Subgroup G)} [IsSmoothRep B]
    [IsSmoothRep B'] (g : B ⟶ B') (n : ℕ) :
    map (.id G) (Rep.coindMap (U : Subgroup G).subtype g) n ≫ shapiroMap U B' n =
      shapiroMap U B n ≫ map (.id (U : Subgroup G)) g n := by
  rw [shapiroMap, shapiroMap, ← map_comp, ← map_comp]
  rfl

end Naturality

instance isSmoothRep_coind_res (A : Rep.{u} k G) [IsSmoothRep A] :
    IsSmoothRep (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A)) :=
  isSmoothRep_coind U _

section Acyclic

variable (X : Type u) [AddCommGroup X] [Module k X]

instance isSmoothRep_coind_discreteCoind :
    IsSmoothRep (Rep.coind (U : Subgroup G).subtype (discreteCoind k (U : Subgroup G) X)) :=
  isSmoothRep_coind U _

noncomputable def coindDiscreteCoindIso :
    Rep.coind (U : Subgroup G).subtype (discreteCoind k (U : Subgroup G) X) ≅
      discreteCoind k G X where
  hom := Rep.ofHom ⟨
    { toFun := fun F => ⟨fun x => (F.1 x) 1,
        (isLocallyConstant_coind U (discreteCoind k (U : Subgroup G) X) F).comp
          fun ψ : LocallyConstant (U : Subgroup G) X => ψ 1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }, fun g => by
        ext F x
        rfl⟩
  inv := Rep.ofHom ⟨
    { toFun := fun φ => ⟨fun x => ⟨fun v => φ ((v : G) * x),
          φ.isLocallyConstant.comp_continuous (continuous_subtype_val.mul continuous_const)⟩,
        fun u x => by
          ext v
          simp [mul_assoc]⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }, fun g => by
        ext φ x v
        change φ ((v : G) * x * g) = φ ((v : G) * (x * g))
        rw [mul_assoc]⟩
  hom_inv_id := by
    ext F x v
    change (F.1 ((v : G) * x)) 1 = F.1 x v
    rw [show (v : G) * x = (U : Subgroup G).subtype v * x from rfl, F.2 v x]
    simp
  inv_hom_id := by
    ext φ x
    change φ (((1 : (U : Subgroup G)) : G) * x) = φ x
    simp

theorem isZero_cohomology_coind_discreteCoind (n : ℕ) :
    IsZero (cohomology (Rep.coind.{u} (U : Subgroup G).subtype
      (discreteCoind k (U : Subgroup G) X)) (n + 1)) :=
  (isZero_cohomology_discreteCoind k G X n).of_iso
    (cohomologyIsoOfIso (coindDiscreteCoindIso U X) (n + 1))

end Acyclic

section DegreeZero

variable (B : Rep.{u} k (U : Subgroup G)) [IsSmoothRep B]

omit [IsTopologicalGroup G] [CompactSpace G] [IsSmoothRep B] in

theorem coind_invariant_apply (f : (Rep.coind (U : Subgroup G).subtype B).ρ.invariants) (x : G) :
    f.1.1 x = f.1.1 1 := by
  have h : f.1.1 (1 * x) = f.1.1 1 :=
    congrArg (fun φ : Rep.coind (U : Subgroup G).subtype B => φ.1 1) (f.2 x)
  rwa [one_mul] at h

noncomputable def coindInvariantsEval :
    (Rep.coind (U : Subgroup G).subtype B).ρ.invariants →ₗ[k] B.ρ.invariants where
  toFun f := ⟨f.1.1 1, fun u => by
    have h := f.1.2 u 1
    simp only [Subgroup.subtype_apply, mul_one] at h
    rw [← h, coind_invariant_apply]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [IsTopologicalGroup G] [CompactSpace G] [IsSmoothRep B] in
theorem coindInvariantsEval_bijective : Function.Bijective (coindInvariantsEval U B) := by
  refine ⟨fun f f' h => ?_, fun b => ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    funext x
    rw [coind_invariant_apply, coind_invariant_apply U B f']
    exact congrArg Subtype.val h
  · refine ⟨⟨⟨fun _ => b.1, fun u _ => (b.2 u).symm⟩, fun g => rfl⟩, rfl⟩

private theorem cocyclesIso₀_hom_comp_f {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (A : Rep.{u} k Γ) [IsSmoothRep A] :
    (cocyclesIso₀ A).hom ≫ ModuleCat.ofHom (invariantsToCochains₀ A) =
      (cochains A).iCycles 0 := by
  dsimp only [cocyclesIso₀, KernelFork.mapIsoOfIsLimit]
  exact (KernelFork.mapOfIsLimit_ι _ _ _).trans (Category.comp_id _)

theorem isIso_shapiroMap_zero : IsIso (shapiroMap U B 0) := by
  set ψ := cochainsMap (A := Rep.coind (U : Subgroup G).subtype B) (B := B)
    (subgroupInclusion (U : Subgroup G)) (coindEvalOne (U : Subgroup G) B)
  have hψ : HomologicalComplex.cyclesMap ψ 0 = (cocyclesIso₀ _).hom ≫
      ModuleCat.ofHom (coindInvariantsEval U B) ≫ (cocyclesIso₀ B).inv := by
    have hK := cocyclesIso₀_hom_comp_f (Rep.coind (U : Subgroup G).subtype B)
    have hL := cocyclesIso₀_hom_comp_f B
    have hinj : Function.Injective ((cochains B).iCycles 0).hom :=
      (ModuleCat.mono_iff_injective _).1 inferInstance
    refine ModuleCat.hom_ext (LinearMap.ext fun z => hinj ?_)
    have e1 := congrArg (fun f => f.hom z) (HomologicalComplex.cyclesMap_i ψ 0)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e1
    rw [e1, ← hL, ← hK]
    set w := (cocyclesIso₀ (Rep.coind (U : Subgroup G).subtype B)).hom.hom z
    have e2 : (cocyclesIso₀ B).hom.hom ((cocyclesIso₀ B).inv.hom (coindInvariantsEval U B w)) =
        coindInvariantsEval U B w := by
      simp
    change (ψ.f 0).hom (invariantsToCochains₀ _ w) =
      invariantsToCochains₀ B ((cocyclesIso₀ B).hom.hom
        ((cocyclesIso₀ B).inv.hom (coindInvariantsEval U B w)))
    rw [e2]
    apply Subtype.ext
    funext x
    rfl
  haveI : IsIso (ModuleCat.ofHom (coindInvariantsEval U B)) :=
    (LinearEquiv.ofBijective _ (coindInvariantsEval_bijective U B)).toModuleIso.isIso_hom
  haveI : IsIso (HomologicalComplex.cyclesMap ψ 0) := by
    rw [hψ]
    infer_instance
  have h := CochainComplex.isoHomologyπ₀_inv_naturality ψ
  have h' : HomologicalComplex.homologyMap ψ 0 = (cochains _).isoHomologyπ₀.inv ≫
      HomologicalComplex.cyclesMap ψ 0 ≫ (cochains B).isoHomologyπ₀.hom := by
    rw [← Category.assoc, ← h, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change IsIso (HomologicalComplex.homologyMap ψ 0)
  rw [h']
  infer_instance

end DegreeZero

section Shapiro

theorem isIso_shapiroMap (n : ℕ) :
    ∀ (B : Rep.{u} k (U : Subgroup G)) [IsSmoothRep B], IsIso (shapiroMap U B n) := by
  induction n with
  | zero => intro B _; exact isIso_shapiroMap_zero U B
  | succ n ih =>
    intro B _
    let X := coindShortComplex B
    have hX : X.ShortExact := coindShortComplex_shortExact B
    have hY : (coindShortComplexOf (U : Subgroup G) X).ShortExact :=
      shortExact_coindShortComplexOf _ hX
    have i1 : IsSmoothRep X.X₁ := isSmoothRep_coindShortComplex_X₁ B
    have i2 : IsSmoothRep X.X₂ := isSmoothRep_coindShortComplex_X₂ B
    have i3 : IsSmoothRep X.X₃ := isSmoothRep_coindShortComplex_X₃ B
    have j1 : IsSmoothRep (coindShortComplexOf (U : Subgroup G) X).X₁ := isSmoothRep_coind U X.X₁
    have j2 : IsSmoothRep (coindShortComplexOf (U : Subgroup G) X).X₂ := isSmoothRep_coind U X.X₂
    have j3 : IsSmoothRep (coindShortComplexOf (U : Subgroup G) X).X₃ := isSmoothRep_coind U X.X₃
    have hcomm : δ hY n (n + 1) rfl ≫ shapiroMap U X.X₁ (n + 1) =
        shapiroMap U X.X₃ n ≫ δ hX n (n + 1) rfl :=
      δ_comp_map (subgroupInclusion (U : Subgroup G))
        (coindEvalOneShortComplex (U : Subgroup G) X) hY hX n (n + 1) rfl

    have hδU : Epi (δ hX n (n + 1) rfl) :=
      (cohomology_exact₁ hX n (n + 1) rfl).epi_f
        ((isZero_cohomology_discreteCoind k (U : Subgroup G) B n).eq_of_tgt _ _)
    have hδG : Epi (δ hY n (n + 1) rfl) :=
      (cohomology_exact₁ hY n (n + 1) rfl).epi_f
        ((isZero_cohomology_coind_discreteCoind U B n).eq_of_tgt _ _)
    have e3 : IsIso (shapiroMap U X.X₃ n) := ih X.X₃
    have e2 : IsIso (shapiroMap U X.X₂ n) := ih X.X₂
    have hepi : Epi (shapiroMap U X.X₁ (n + 1)) := by
      have : Epi (δ hY n (n + 1) rfl ≫ shapiroMap U X.X₁ (n + 1)) := by
        rw [hcomm]
        exact @epi_comp _ _ _ _ _ (shapiroMap U X.X₃ n) (@IsIso.epi_of_iso _ _ _ _ _ e3)
          (δ hX n (n + 1) rfl) hδU
      exact epi_of_epi (δ hY n (n + 1) rfl) _
    have hmono : Mono (shapiroMap U X.X₁ (n + 1)) := by
      rw [ModuleCat.mono_iff_injective, injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective _).1 hδG x
      have h1 : (δ hX n (n + 1) rfl).hom ((shapiroMap U X.X₃ n).hom y) = 0 := by
        have := congrArg (fun f => f.hom y) hcomm
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
        rw [← this, hx]
      obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1
        (cohomology_exact₃ hX n (n + 1) rfl) _ h1
      obtain ⟨z', rfl⟩ := (ModuleCat.epi_iff_surjective _).1
        (@IsIso.epi_of_iso _ _ _ _ (shapiroMap U X.X₂ n) e2) z
      have h2 : (shapiroMap U X.X₃ n).hom
          ((map (.id G) (coindShortComplexOf (U : Subgroup G) X).g n).hom z') =
          (shapiroMap U X.X₃ n).hom y := by
        have := congrArg (fun f => f.hom z') (shapiroMap_naturality U X.g n)
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
        exact this.trans hz
      have hinj := (ModuleCat.mono_iff_injective _).1
        (@IsIso.mono_of_iso _ _ _ _ (shapiroMap U X.X₃ n) e3)
      rw [← hinj h2]
      have := congrArg (fun f => f.hom z') (comp_δ hY n (n + 1) rfl)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
        LinearMap.zero_apply] at this
      exact this
    show IsIso (shapiroMap U X.X₁ (n + 1))
    exact @isIso_of_mono_of_epi _ _ _ _ _ _ hmono hepi

instance isIso_shapiroMap' (B : Rep.{u} k (U : Subgroup G)) [IsSmoothRep B] (n : ℕ) :
    IsIso (shapiroMap U B n) :=
  isIso_shapiroMap U n B

noncomputable def shapiroIso (B : Rep.{u} k (U : Subgroup G)) [IsSmoothRep B] (n : ℕ) :
    cohomology (Rep.coind (U : Subgroup G).subtype B) n ≅ cohomology B n :=
  asIso (shapiroMap U B n)

@[simp]
theorem shapiroIso_hom (B : Rep.{u} k (U : Subgroup G)) [IsSmoothRep B] (n : ℕ) :
    (shapiroIso U B n).hom = shapiroMap U B n :=
  rfl

end Shapiro


end Langlands.ProfiniteCohomology
