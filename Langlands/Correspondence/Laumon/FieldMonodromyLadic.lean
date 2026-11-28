import Langlands.MathlibBase
import Langlands.Correspondence.Laumon.FieldMonodromy
import Langlands.Correspondence.HenniartLadicTransport
import Langlands.Sheaf.LisseMonodromyTransport
import Langlands.Sheaf.LisseTensorStalk
import Langlands.Sheaf.AdicStalkExact

/-!
# ℓ-adic monodromy over a field, from the homeomorphism onto the fundamental group

For a field `K` with separable closure `Ω`, this module proves the clauses of
`Langlands.Henniart.Laumon.LadicFieldMonodromyStatement` for the monodromy functor
`fieldMonodromyFunctor ℓ K Ω`, assuming that `fieldGaloisToAut K Ω` is a homeomorphism, and
assembles them into `Langlands.Henniart.Laumon.ladicFieldMonodromyStatement_of_isHomeomorph`.
-/

noncomputable section

universe u uW

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.Henniart.Laumon

open Langlands.Henniart.LocalNumerical

section Field

variable (ℓ : ℕ) [Fact ℓ.Prime] (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω]

local notation "E" => PadicAlgCl ℓ

omit [IsSepClosure K Ω] in
/-- weil-conjectures's monodromy of lisse sheaves on `Spec K` is an equivalence at the geometric
point `fieldGeometricPoint K Ω`. -/
theorem fieldMonodromy_isEquivalenceAt :
    (ProEtale.universalLisseMonodromy ℓ (Spec (.of K)) Ω).IsEquivalenceAt
      (fieldGeometricPoint K Ω) :=
  ProEtale.universalLisseMonodromy_isEquivalenceAt ℓ (Spec (.of K)) Ω _

/-- The monodromy functor is faithful. -/
theorem fieldMonodromyFunctor_faithful : (fieldMonodromyFunctor ℓ K Ω).Faithful :=
  ⟨fun {G H} a b h => by
    have h' := congrArg (fun x => (FiniteRepresentation.homEquiv _ _ x).toLinearMap) h
    simp only [fieldMonodromyFunctor] at h'
    exact (fieldMonodromy_isEquivalenceAt ℓ K Ω).ext_of_lisseStalkMap h'⟩

variable {K Ω}

/-- The matrix coefficients of the monodromy representation are continuous. -/
theorem continuous_fieldMonodromy_coeff (hf : Continuous (fieldGaloisToAut K Ω))
    (G : ProEtale.LisseSheaf ℓ (Spec (.of K)))
    (φ : Module.Dual E (ProEtale.LisseMonodromy.StalkSpace (fieldGeometricPoint K Ω) G))
    (v : ProEtale.LisseMonodromy.StalkSpace (fieldGeometricPoint K Ω) G) :
    Continuous fun σ => φ (fieldMonodromy ℓ K Ω G σ v) :=
  (fieldMonodromy_isEquivalenceAt ℓ K Ω).continuous_rep_comp _ hf G φ v

/-- The monodromy representations satisfy `IsLadicContinuous`. -/
theorem isLadicContinuous_fieldMonodromyRepresentation (hf : Continuous (fieldGaloisToAut K Ω))
    (G : ProEtale.LisseSheaf ℓ (Spec (.of K))) :
    IsLadicContinuous ℓ (fieldMonodromyRepresentation ℓ K Ω G) :=
  (isLadicContinuous_iff ℓ _).2 (continuous_fieldMonodromy_coeff ℓ hf G)

/-- Compactness of the Galois group gives a finite extension of `ℚ_ℓ` over which the monodromy
representations are defined. -/
theorem isLadicDefinedOverFiniteExtension_fieldMonodromyRepresentation
    (hf : IsHomeomorph (fieldGaloisToAut K Ω)) (G : ProEtale.LisseSheaf ℓ (Spec (.of K))) :
    IsLadicDefinedOverFiniteExtension ℓ (fieldMonodromyRepresentation ℓ K Ω G) := by
  have : CompactSpace Gal(Ω/K) := hf.homeomorph.symm.compactSpace
  exact (isLadicContinuous_fieldMonodromyRepresentation ℓ hf.continuous G).isLadicDefinedOverFiniteExtension ℓ

/-- The monodromy functor is full. -/
theorem fieldMonodromyFunctor_full (hf : Function.Surjective (fieldGaloisToAut K Ω)) :
    (fieldMonodromyFunctor ℓ K Ω).Full :=
  ⟨fun {G H} φ => by
    obtain ⟨a, ha⟩ := (fieldMonodromy_isEquivalenceAt ℓ K Ω).full_comp (fieldGaloisToAut K Ω) hf
      (FiniteRepresentation.homEquiv _ _ φ).toLinearMap fun σ v =>
        LinearMap.congr_fun ((FiniteRepresentation.homEquiv _ _ φ).isIntertwining' σ) v
    refine ⟨a, (FiniteRepresentation.homEquiv _ _).injective ?_⟩
    refine (Equiv.apply_symm_apply (FiniteRepresentation.homEquiv _ _) _).trans ?_
    exact Representation.IntertwiningMap.ext ha⟩

/-- **Essential surjectivity.** Every continuous finite-dimensional representation of
`Ω ≃ₐ[K] Ω` over `ℚ̄_ℓ`, in any carrier universe, is equivalent to a monodromy representation. -/
theorem exists_fieldMonodromyRepresentation_equiv (hf : IsHomeomorph (fieldGaloisToAut K Ω))
    (A : FiniteRepresentation.{0, u, uW} E Gal(Ω/K)) (hA : IsLadicContinuous ℓ A) :
    ∃ G : ProEtale.LisseSheaf ℓ (Spec (.of K)),
      Nonempty (FiniteRepresentation.Equiv (fieldMonodromyRepresentation ℓ K Ω G) A) := by
  obtain ⟨B, ⟨e⟩⟩ : ∃ B : FiniteRepresentation.{0, u, u + 1} E Gal(Ω/K),
      Nonempty (FiniteRepresentation.Equiv A B) := exists_finiteRepresentation_equiv ℓ A
  have hB := (isLadicContinuous_iff ℓ B).1 (hA.of_equiv ℓ e)
  obtain ⟨G, e', he'⟩ := (fieldMonodromy_isEquivalenceAt ℓ K Ω).essSurj_comp
    (fieldGaloisToAut K Ω) hf B B.representation hB
  exact ⟨G, ⟨(Representation.Equiv.mk e' fun σ => LinearMap.ext fun v => he' σ v).trans e.symm⟩⟩

/-- **Simple lisse sheaves are those with irreducible monodromy.** -/
theorem simple_iff_isIrreducible_fieldMonodromy (hf : Function.Surjective (fieldGaloisToAut K Ω))
    (G : ProEtale.LisseSheaf ℓ (Spec (.of K))) :
    Simple G ↔ Representation.IsIrreducible (fieldMonodromy ℓ K Ω G) :=
  ((fieldMonodromy_isEquivalenceAt ℓ K Ω).simple_iff_isIrreducible G).trans
    (ProEtale.LisseMonodromy.IsEquivalenceAt.isIrreducible_comp_iff
      (fieldGaloisToAut K Ω) hf G).symm

variable (K Ω)

omit [IsSepClosure K Ω] in
/-- **Exactness.** The stalk maps of a short exact sequence of `ℓ`-adic sheaves on `Spec K` form a
short exact sequence. -/
theorem adicStalkMap_shortExact_field (S : ShortComplex (ProEtale.AdicSheaf ℓ (Spec (.of K))))
    (hS : S.ShortExact) :
    Function.Injective (adicStalkMap ℓ K Ω S.f) ∧ Function.Surjective (adicStalkMap ℓ K Ω S.g) ∧
      LinearMap.range (adicStalkMap ℓ K Ω S.f) = LinearMap.ker (adicStalkMap ℓ K Ω S.g) :=
  ProEtale.adicStalkMap_shortExact (fieldGeometricPoint K Ω) hS

end Field

section Tensor

variable (ℓ : ℕ) [Fact ℓ.Prime] {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω]

local notation "E" => PadicAlgCl ℓ

omit [IsSepClosure K Ω] in
/-- The tensor product over `ℚ̄_ℓ` of two lisse sheaves on `Spec K` is lisse. -/
theorem isAdicLisseSheaf_tensorLeft_field (G H : ProEtale.LisseSheaf ℓ (Spec (.of K))) :
    ProEtale.IsAdicLisseSheaf ((CategoryTheory.Mod.tensorLeft H.obj).obj G.obj) :=
  ProEtale.IsAdicLisseSheaf.tensorLeft G.property H.property

omit [IsSepClosure K Ω] in
/-- The `ℚ̄_ℓ`-linear comparison `G_t ⊗ H_t → (G ⊗ H)_t` of stalks at `fieldGeometricPoint K Ω`. -/
noncomputable def fieldTensorStalkMap (G H : ProEtale.LisseSheaf ℓ (Spec (.of K))) :
    TensorProduct E (ProEtale.LisseMonodromy.StalkSpace (fieldGeometricPoint K Ω) G)
        (ProEtale.LisseMonodromy.StalkSpace (fieldGeometricPoint K Ω) H) →ₗ[E]
      ProEtale.LisseMonodromy.StalkSpace (fieldGeometricPoint K Ω)
        ⟨_, isAdicLisseSheaf_tensorLeft_field ℓ G H⟩ :=
  ((WeilCoefficients.toModuleCat ℓ).map
      (ProEtale.tensorStalkMap (fieldGeometricPoint K Ω) G.obj H.obj)).hom ∘ₗ
    WeilCoefficients.tensorRestrict ((ProEtale.lisseStalk ℓ (fieldGeometricPoint K Ω)).obj G)
      ((ProEtale.lisseStalk ℓ (fieldGeometricPoint K Ω)).obj H)

omit [IsSepClosure K Ω] in
lemma fieldTensorStalkMap_tmul (G H : ProEtale.LisseSheaf ℓ (Spec (.of K)))
    (g : ProEtale.LisseMonodromy.StalkSpace (fieldGeometricPoint K Ω) G)
    (h : ProEtale.LisseMonodromy.StalkSpace (fieldGeometricPoint K Ω) H) :
    fieldTensorStalkMap ℓ G H (g ⊗ₜ h) =
      (ProEtale.tensorStalkMap (fieldGeometricPoint K Ω) G.obj H.obj).hom
        (WeilCoefficients.ofToModuleCat g ⊗ₜ WeilCoefficients.ofToModuleCat h) :=
  congrArg ((WeilCoefficients.toModuleCat ℓ).map
      (ProEtale.tensorStalkMap (fieldGeometricPoint K Ω) G.obj H.obj)).hom
    (WeilCoefficients.tensorRestrict_tmul _ _ g h)

omit [IsSepClosure K Ω] in
/-- Compatibility of the stalk functor at a point with values in `Ω̄` with tensor products of
lisse sheaves makes the comparison bijective. -/
lemma fieldTensorStalkMap_bijective (G H : ProEtale.LisseSheaf ℓ (Spec (.of K))) :
    Function.Bijective (fieldTensorStalkMap (Ω := Ω) ℓ G H) := by
  have : IsIso (ProEtale.tensorStalkMap (fieldGeometricPoint K Ω) G.obj H.obj) :=
    ProEtale.isIso_tensorStalkMap _ _ H.property
  exact (ConcreteCategory.bijective_of_isIso ((WeilCoefficients.toModuleCat ℓ).map
    (ProEtale.tensorStalkMap (fieldGeometricPoint K Ω) G.obj H.obj))).comp
    (WeilCoefficients.tensorRestrict_bijective _ _)

/-- The comparison of stalks intertwines the monodromy of `G ⊗ H` with the tensor product of the
monodromies of `G` and `H`. -/
lemma fieldTensorStalkMap_fieldMonodromy (G H : ProEtale.LisseSheaf ℓ (Spec (.of K)))
    (σ : Gal(Ω/K)) (x : TensorProduct E
      (ProEtale.LisseMonodromy.StalkSpace (fieldGeometricPoint K Ω) G)
      (ProEtale.LisseMonodromy.StalkSpace (fieldGeometricPoint K Ω) H)) :
    fieldMonodromy ℓ K Ω ⟨_, isAdicLisseSheaf_tensorLeft_field ℓ G H⟩ σ
        (fieldTensorStalkMap ℓ G H x) =
      fieldTensorStalkMap ℓ G H
        (((fieldMonodromy ℓ K Ω G).tprod (fieldMonodromy ℓ K Ω H)) σ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul g h =>
    rw [Representation.tprod_apply, TensorProduct.map_tmul, fieldTensorStalkMap_tmul,
      fieldTensorStalkMap_tmul]
    exact (ProEtale.universalLisseMonodromy ℓ (Spec (.of K)) Ω).mono_tensorStalkMap _ G H
      (isAdicLisseSheaf_tensorLeft_field ℓ G H) _ _
  | add x y hx hy => simp only [map_add, hx, hy]

omit [IsSepClosure K Ω] in
/-- The comparison of stalks is natural in both lisse sheaves. -/
lemma fieldTensorStalkMap_naturality {G G' H H' : ProEtale.LisseSheaf ℓ (Spec (.of K))}
    (a : G ⟶ G') (b : H ⟶ H') (x : TensorProduct E
      (ProEtale.LisseMonodromy.StalkSpace (fieldGeometricPoint K Ω) G)
      (ProEtale.LisseMonodromy.StalkSpace (fieldGeometricPoint K Ω) H)) :
    adicStalkMap ℓ K Ω ((CategoryTheory.Mod.tensorLeft H.obj).map a.hom ≫
        (CategoryTheory.Mod.tensorLeftMap b.hom).app G'.obj) (fieldTensorStalkMap ℓ G H x) =
      fieldTensorStalkMap ℓ G' H'
        (TensorProduct.map (lisseStalkMap ℓ K Ω a) (lisseStalkMap ℓ K Ω b) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul g h =>
    rw [TensorProduct.map_tmul, fieldTensorStalkMap_tmul, fieldTensorStalkMap_tmul]
    have := congrArg (fun m => m.hom (WeilCoefficients.ofToModuleCat g ⊗ₜ
        WeilCoefficients.ofToModuleCat h))
      (ProEtale.tensorStalkMap_naturality (fieldGeometricPoint K Ω) a.hom b.hom)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleCat.MonoidalCategory.tensorHom_tmul] at this
    exact this.symm
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **Tensor products.** Clause 5 of `LadicFieldMonodromyStatement`. -/
theorem fieldMonodromy_tensor :
    ∃ (hl : ∀ G H : ProEtale.LisseSheaf ℓ (Spec (.of K)),
          ProEtale.IsAdicLisseSheaf ((CategoryTheory.Mod.tensorLeft H.obj).obj G.obj))
        (θ : ∀ G H : ProEtale.LisseSheaf ℓ (Spec (.of K)),
          ProEtale.LisseMonodromy.StalkSpace (fieldGeometricPoint K Ω)
              ⟨(CategoryTheory.Mod.tensorLeft H.obj).obj G.obj, hl G H⟩ ≃ₗ[PadicAlgCl ℓ]
            TensorProduct (PadicAlgCl ℓ)
              (ProEtale.LisseMonodromy.StalkSpace (fieldGeometricPoint K Ω) G)
              (ProEtale.LisseMonodromy.StalkSpace (fieldGeometricPoint K Ω) H)),
      (∀ (G H : ProEtale.LisseSheaf ℓ (Spec (.of K))) (σ : Gal(Ω/K)) v,
        θ G H (fieldMonodromy ℓ K Ω ⟨_, hl G H⟩ σ v) =
          ((fieldMonodromy ℓ K Ω G).tprod (fieldMonodromy ℓ K Ω H)) σ (θ G H v)) ∧
      ∀ (G G' H H' : ProEtale.LisseSheaf ℓ (Spec (.of K))) (f : G ⟶ G') (g : H ⟶ H') v,
        θ G' H' (adicStalkMap ℓ K Ω ((CategoryTheory.Mod.tensorLeft H.obj).map f.hom ≫
            (CategoryTheory.Mod.tensorLeftMap g.hom).app G'.obj) v) =
          TensorProduct.map (lisseStalkMap ℓ K Ω f) (lisseStalkMap ℓ K Ω g) (θ G H v) := by
  refine ⟨isAdicLisseSheaf_tensorLeft_field ℓ, fun G H =>
    (LinearEquiv.ofBijective _ (fieldTensorStalkMap_bijective ℓ G H)).symm,
    fun G H σ v => ?_, fun G G' H H' a b v => ?_⟩
  · obtain ⟨x, rfl⟩ := (fieldTensorStalkMap_bijective (Ω := Ω) ℓ G H).2 v
    rw [fieldTensorStalkMap_fieldMonodromy]
    erw [LinearEquiv.ofBijective_symm_apply_apply, LinearEquiv.ofBijective_symm_apply_apply]
  · obtain ⟨x, rfl⟩ := (fieldTensorStalkMap_bijective (Ω := Ω) ℓ G H).2 v
    rw [fieldTensorStalkMap_naturality]
    erw [LinearEquiv.ofBijective_symm_apply_apply, LinearEquiv.ofBijective_symm_apply_apply]

end Tensor

section LocalField

variable (ℓ : ℕ) [Fact ℓ.Prime] {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {Ω : Type u} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

local notation "E" => PadicAlgCl ℓ

/-- **Simple lisse sheaves and irreducible ℓ-adic classes.** The second conjunct of
`LadicFieldMonodromyStatement`. -/
theorem fieldMonodromy_irreducibleLadicClass (hf : IsHomeomorph (fieldGaloisToAut K Ω))
    (n : ℕ+) :
    (∀ c : IrreducibleLadicClass.{u, u, uW} K Ω ℓ n, ∃ G : ProEtale.LisseSheaf ℓ (Spec (.of K)),
      Simple G ∧ ∀ A : FiniteRepresentation.{0, u, uW} (PadicAlgCl ℓ) Gal(Ω/K),
        ladicClassForget K Ω ℓ c = FiniteRepresentation.classOf A →
          Nonempty (FiniteRepresentation.Equiv (fieldMonodromyRepresentation ℓ K Ω G) A)) ∧
    ∀ G : ProEtale.LisseSheaf ℓ (Spec (.of K)), Simple G →
      (fieldMonodromyRepresentation ℓ K Ω G).rank = n →
        ∃ c : IrreducibleLadicClass.{u, u, uW} K Ω ℓ n,
          ∀ A : FiniteRepresentation.{0, u, uW} (PadicAlgCl ℓ) Gal(Ω/K),
            ladicClassForget K Ω ℓ c = FiniteRepresentation.classOf A →
              Nonempty (FiniteRepresentation.Equiv (fieldMonodromyRepresentation ℓ K Ω G) A) := by
  refine ⟨fun c => ?_, fun G hG hrank => ?_⟩
  · obtain ⟨c, hc⟩ := c
    obtain ⟨⟨A, hcont, -, hirr⟩, rfl⟩ := Quotient.exists_rep c
    obtain ⟨G, ⟨e⟩⟩ := exists_fieldMonodromyRepresentation_equiv ℓ hf A hcont
    refine ⟨G, (simple_iff_isIrreducible_fieldMonodromy ℓ hf.surjective G).2
      (isIrreducible_of_equiv ℓ e.symm hirr), fun A' hA' => ?_⟩
    obtain ⟨e'⟩ := (FiniteRepresentation.classOf_eq_iff A A').1 hA'
    exact ⟨e.trans e'⟩
  · obtain ⟨B, ⟨e⟩⟩ : ∃ B : FiniteRepresentation.{0, u, uW} E Gal(Ω/K),
        Nonempty (FiniteRepresentation.Equiv (fieldMonodromyRepresentation ℓ K Ω G) B) :=
      exists_finiteRepresentation_equiv ℓ _
    have h₁ := (isLadicContinuous_fieldMonodromyRepresentation ℓ hf.continuous G).of_equiv ℓ e
    have h₂ := (isLadicDefinedOverFiniteExtension_fieldMonodromyRepresentation ℓ hf G).of_equiv ℓ e
    have h₃ := isIrreducible_of_equiv ℓ e
      ((simple_iff_isIrreducible_fieldMonodromy ℓ hf.surjective G).1 hG)
    refine ⟨⟨Quotient.mk _ ⟨B, h₁, h₂, h₃⟩, ?_⟩, fun A hA => ?_⟩
    · change B.rank = (n : ℕ)
      rw [← FiniteRepresentation.rank_eq_of_equiv e, hrank]
    · obtain ⟨e'⟩ := (FiniteRepresentation.classOf_eq_iff B A).1 hA
      exact ⟨e.trans e'⟩

end LocalField

/-- **ℓ-adic monodromy of a field, from the homeomorphism onto the fundamental group.** If
`fieldGaloisToAut K Ω` is a homeomorphism for every field `K` and separable closure `Ω`, then
`LadicFieldMonodromyStatement` holds. -/
theorem ladicFieldMonodromyStatement_of_isHomeomorph
    (h : ∀ (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω],
      IsHomeomorph (fieldGaloisToAut K Ω)) :
    LadicFieldMonodromyStatement.{u, uW} := by
  refine ⟨fun ℓ _ K Ω _ _ _ _ => ?_, fun ℓ _ K _ _ _ _ Ω _ _ _ n =>
    fieldMonodromy_irreducibleLadicClass ℓ (h K Ω) n⟩
  have hf := h K Ω
  exact ⟨fun G => ⟨isLadicContinuous_fieldMonodromyRepresentation ℓ hf.continuous G,
      isLadicDefinedOverFiniteExtension_fieldMonodromyRepresentation ℓ hf G⟩,
    fieldMonodromyFunctor_full ℓ hf.surjective, fieldMonodromyFunctor_faithful ℓ K Ω,
    fun A hA _ => exists_fieldMonodromyRepresentation_equiv ℓ hf A hA,
    fun S _ _ _ hS => adicStalkMap_shortExact_field ℓ K Ω S hS, fieldMonodromy_tensor ℓ,
    fun G => simple_iff_isIrreducible_fieldMonodromy ℓ hf.surjective G⟩

end Langlands.Henniart.Laumon
