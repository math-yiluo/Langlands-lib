import Langlands.MathlibBase
import Langlands.Correspondence.HenniartLadicClasses
import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExtension
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.GaloisAction
import WeilConjectures.AlgebraicGeometry.EtaleSheafDiscreteContinuousRep

/-!
# Monodromy over a field: the bridge (b1)

For a field `K` with separable closure `Ω`, Laumon (1987, (2.1.2)–(2.1.2.1)) identifies sheaves
on `Spec K` with Galois modules through the fibre functor at a geometric point. This module
fixes the geometric point `Spec Ω̄ → Spec Ω → Spec K` with `Ω̄ = AlgebraicClosure Ω`, transports
weil-conjectures's action of `Ω̄ ≃ₐ[K] Ω̄` on the finite étale fibre functor to `Ω ≃ₐ[K] Ω`,
defines the monodromy representation of an arithmetic lisse `ℚ̄_ℓ`-sheaf on `Spec K` as a
`Langlands.FiniteRepresentation` of `Ω ≃ₐ[K] Ω`, and states the comparison theorems at finite
level and in the ℓ-adic lisse category.
-/

noncomputable section

universe u uW

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.Henniart.Laumon

open Langlands.Henniart.LocalNumerical

section Galois

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- Restriction of `K`-automorphisms of `AlgebraicClosure Ω` to `Ω`. -/
def algebraicClosureRestriction : Gal(AlgebraicClosure Ω/K) →* Gal(Ω/K) :=
  AlgEquiv.restrictNormalHom Ω

/-- Restriction to `Ω` is bijective: automorphisms extend since `AlgebraicClosure Ω` is normal
over `K`, and uniquely since it is purely inseparable over the separably closed `Ω`. -/
theorem algebraicClosureRestriction_bijective :
    Function.Bijective (algebraicClosureRestriction K Ω) := by
  have := IsSepClosure.sep_closed K (K := Ω)
  refine ⟨fun σ τ h => ?_, AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure Ω)⟩
  have : IsPurelyInseparable Ω (AlgebraicClosure Ω) :=
    Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed
  have hστ : (σ : AlgebraicClosure Ω →+* AlgebraicClosure Ω).comp
      (algebraMap Ω (AlgebraicClosure Ω)) =
      (τ : AlgebraicClosure Ω →+* AlgebraicClosure Ω).comp (algebraMap Ω (AlgebraicClosure Ω)) := by
    ext x
    have h' : σ.restrictNormal Ω = τ.restrictNormal Ω := h
    change σ (algebraMap Ω (AlgebraicClosure Ω) x) = τ (algebraMap Ω (AlgebraicClosure Ω) x)
    rw [← AlgEquiv.restrictNormal_commutes σ Ω x, ← AlgEquiv.restrictNormal_commutes τ Ω x, h']
  exact AlgEquiv.ext (RingHom.congr_fun
    (IsPurelyInseparable.injective_comp_algebraMap Ω (AlgebraicClosure Ω) (AlgebraicClosure Ω) hστ))

/-- The unique extension of `K`-automorphisms of `Ω` to `AlgebraicClosure Ω`. -/
def fieldGaloisLift : Gal(Ω/K) ≃* Gal(AlgebraicClosure Ω/K) :=
  (MulEquiv.ofBijective _ (algebraicClosureRestriction_bijective K Ω)).symm

/-- The geometric point `Spec Ω̄ → Spec Ω → Spec K`, with `Ω̄ = AlgebraicClosure Ω`. -/
abbrev fieldGeometricPoint : Spec (.of (AlgebraicClosure Ω)) ⟶ Spec (.of K) :=
  Scheme.FiniteEtale.pointOfAlgebra (AlgebraicClosure Ω) (𝟙 (Spec (.of K)))

/-- The action of `Ω ≃ₐ[K] Ω` on the finite étale fibre functor at `fieldGeometricPoint K Ω`:
the unique extension to `Ω̄` followed by weil-conjectures's `galoisToAut`, which acts by
precomposition with `Spec σ`. -/
def fieldGaloisToAut :
    Gal(Ω/K) →* Aut (Scheme.FiniteEtale.fiber (fieldGeometricPoint K Ω)) :=
  (Scheme.FiniteEtale.galoisToAut (Ω := AlgebraicClosure Ω) (𝟙 (Spec (.of K)))).comp
    (fieldGaloisLift K Ω).toMonoidHom

end Galois

section Ladic

variable (ℓ : ℕ) [Fact ℓ.Prime] (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω]

local notation "E" => PadicAlgCl ℓ

/-- The monodromy representation of `Ω ≃ₐ[K] Ω` on the stalk of an arithmetic lisse sheaf at
`fieldGeometricPoint K Ω`, for weil-conjectures's `universalLisseMonodromy`. -/
def fieldMonodromy (G : ProEtale.LisseSheaf ℓ (Spec (.of K))) :
    Representation E Gal(Ω/K)
      (ProEtale.LisseMonodromy.StalkSpace (fieldGeometricPoint K Ω) G) :=
  ((ProEtale.universalLisseMonodromy ℓ (Spec (.of K)) Ω).rep (fieldGeometricPoint K Ω) G).comp
    (fieldGaloisToAut K Ω)

/-- The monodromy representation as a `Langlands.FiniteRepresentation`, on the stalk itself. -/
def fieldMonodromyRepresentation (G : ProEtale.LisseSheaf ℓ (Spec (.of K))) :
    FiniteRepresentation.{0, u, u + 1} E Gal(Ω/K) :=
  FiniteRepresentation.of (fieldMonodromy ℓ K Ω G)

/-- The `E`-linear map of stalks of a morphism of lisse sheaves. -/
def lisseStalkMap {G H : ProEtale.LisseSheaf ℓ (Spec (.of K))} (f : G ⟶ H) :
    ProEtale.LisseMonodromy.StalkSpace (fieldGeometricPoint K Ω) G →ₗ[E]
      ProEtale.LisseMonodromy.StalkSpace (fieldGeometricPoint K Ω) H :=
  ((WeilCoefficients.toModuleCat ℓ).map
    ((ProEtale.lisseStalk ℓ (fieldGeometricPoint K Ω)).map f)).hom

/-- The monodromy functor from arithmetic lisse sheaves on `Spec K` to finite-dimensional
`E`-representations of `Ω ≃ₐ[K] Ω`. -/
def fieldMonodromyFunctor :
    ProEtale.LisseSheaf ℓ (Spec (.of K)) ⥤ FiniteRepresentation.{0, u, u + 1} E Gal(Ω/K) where
  obj G := fieldMonodromyRepresentation ℓ K Ω G
  map {G H} f := (FiniteRepresentation.homEquiv _ _).symm
    { lisseStalkMap ℓ K Ω f with
      isIntertwining' := fun g => LinearMap.ext fun v =>
        ProEtale.LisseMonodromy.rep_naturality _ _ f (fieldGaloisToAut K Ω g) v }
  map_id G := by
    apply (FiniteRepresentation.homEquiv _ _).injective
    ext v
    change ((WeilCoefficients.toModuleCat ℓ).map
      ((ProEtale.lisseStalk ℓ (fieldGeometricPoint K Ω)).map (𝟙 G))).hom v = v
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    apply (FiniteRepresentation.homEquiv _ _).injective
    ext v
    change ((WeilCoefficients.toModuleCat ℓ).map
      ((ProEtale.lisseStalk ℓ (fieldGeometricPoint K Ω)).map (f ≫ g))).hom v =
        lisseStalkMap ℓ K Ω g (lisseStalkMap ℓ K Ω f v)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    rfl

/-- The `E`-linear map of stalks at `fieldGeometricPoint K Ω` of a morphism of `ℓ`-adic
sheaves. -/
def adicStalkMap {G H : ProEtale.AdicSheaf ℓ (Spec (.of K))} (f : G ⟶ H) :
    (WeilCoefficients.toModuleCat ℓ).obj
        ((ProEtale.stalkFunctor ℓ (fieldGeometricPoint K Ω)).obj
          ((ProEtale.AdicSheaf.forget (Spec (.of K))).obj G)) →ₗ[E]
      (WeilCoefficients.toModuleCat ℓ).obj
        ((ProEtale.stalkFunctor ℓ (fieldGeometricPoint K Ω)).obj
          ((ProEtale.AdicSheaf.forget (Spec (.of K))).obj H)) :=
  ((WeilCoefficients.toModuleCat ℓ).map ((ProEtale.stalkFunctor ℓ (fieldGeometricPoint K Ω)).map
    ((ProEtale.AdicSheaf.forget (Spec (.of K))).map f))).hom

end Ladic

/-- **Finite étale monodromy of a field.** The action `fieldGaloisToAut K Ω` is an isomorphism
of the Krull-topologized `Ω ≃ₐ[K] Ω` onto the automorphism group of the finite étale fibre
functor with its profinite topology. For every commutative ring `Λ`, the étale sheaves of
`Λ`-modules on `Spec K` are equivalent to the discrete continuous `Λ`-representations of
`Ω ≃ₐ[K] Ω`, by an equivalence whose underlying module is the stalk at `Spec Ω → Spec K` and
under which `σ` sends the germ of a section at a lift `x` to its germ at `Spec σ ≫ x`. For a
field extension `L` of `K` with a separable closure `Ω_L` and a `K`-embedding `ι : Ω → Ω_L`, the
stalk at `Spec Ω → Spec K` is identified with the stalk at `Spec Ω_L → Spec K` by germs, and
under this identification the action of `σ` is the transport action of every `τ` in the Galois
group of `Ω_L/L` restricting to `σ`: inverse image to `Spec L` corresponds to restriction. -/
def FiniteEtaleFieldMonodromyStatement : Prop :=
  ∀ (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω],
    IsHomeomorph (fieldGaloisToAut K Ω) ∧
    ∀ (Λ : Type u) [CommRing Λ],
      letI := IsSepClosure.sep_closed K (K := Ω)
      ∃ (e : Sheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ) ≌
          Rep.DiscreteContinuousRep.{u, u, u + 1} Λ Gal(Ω/K))
        (i : e.functor ⋙ ObjectProperty.ι _ ⋙ forget₂ (Rep.{u + 1} Λ Gal(Ω/K))
            (ModuleCat.{u + 1} Λ) ≅
          (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber),
        (∀ (F : Sheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) (σ : Gal(Ω/K))
          (X : (Spec (.of K)).Etale)
          (x x' : (Scheme.pointSmallEtale
            (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X),
          x'.left = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x.left →
          ∀ z : F.obj.obj (op X),
            i.hom.app F ((e.functor.obj F).obj.ρ σ (i.inv.app F
              ((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber
                X x F.obj z))) =
            (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber
              X x' F.obj z) ∧
        ∀ (L : Type u) [Field L] [Algebra K L] (ΩL : Type u) [Field ΩL] [Algebra L ΩL]
          [IsSepClosure L ΩL] [Algebra K ΩL] [IsScalarTower K L ΩL] (ι : Ω →ₐ[K] ΩL)
          (F : Sheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ)),
          letI := IsSepClosure.sep_closed L (K := ΩL)
          ∃ c : (Scheme.pointSmallEtale
                (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber.obj F ≅
              (Scheme.pointSmallEtale
                (Spec.map (CommRingCat.ofHom (algebraMap K ΩL)))).sheafFiber.obj F,
            (∀ (X : (Spec (.of K)).Etale)
              (x : (Scheme.pointSmallEtale
                (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X)
              (y : (Scheme.pointSmallEtale
                (Spec.map (CommRingCat.ofHom (algebraMap K ΩL)))).fiber.obj X),
              y.left = Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ x.left →
              ∀ z : F.obj.obj (op X),
                c.hom ((Scheme.pointSmallEtale
                    (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber X x F.obj z) =
                  (Scheme.pointSmallEtale
                    (Spec.map (CommRingCat.ofHom (algebraMap K ΩL)))).toPresheafFiber X y F.obj z) ∧
            ∀ (τ : Gal(ΩL/L)) (σ : Gal(Ω/K)), (∀ a, ι (σ a) = τ (ι a)) →
              ∀ (X : (Spec (.of K)).Etale)
                (x : (Scheme.pointSmallEtale
                  (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X)
                (y : (Scheme.pointSmallEtale
                  (Spec.map (CommRingCat.ofHom (algebraMap K ΩL)))).fiber.obj X),
                y.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
                  Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ x.left →
                ∀ z : F.obj.obj (op X),
                  c.hom (i.hom.app F ((e.functor.obj F).obj.ρ σ (i.inv.app F
                    ((Scheme.pointSmallEtale
                      (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber
                        X x F.obj z)))) =
                    (Scheme.pointSmallEtale
                      (Spec.map (CommRingCat.ofHom (algebraMap K ΩL)))).toPresheafFiber X y F.obj z

/-- **ℓ-adic monodromy of a field.** For every field `K` with separable closure `Ω`, the
monodromy functor has values satisfying `IsLadicContinuous` and
`IsLadicDefinedOverFiniteExtension`, is full and faithful, reaches every such representation in
every carrier universe, sends short exact sequences of lisse sheaves to short exact sequences of
stalks, is compatible with the tensor product `⊗` over `ℚ̄_ℓ` through isomorphisms natural in
both sheaves, and matches simple objects with
irreducible representations. For a nonarchimedean local field `K`, it identifies the simple
lisse sheaves of rank `n` with `IrreducibleLadicClass K Ω ℓ n`. -/
def LadicFieldMonodromyStatement : Prop :=
  (∀ (ℓ : ℕ) [Fact ℓ.Prime] (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
      [IsSepClosure K Ω],
    (∀ G : ProEtale.LisseSheaf ℓ (Spec (.of K)),
      IsLadicContinuous ℓ (fieldMonodromyRepresentation ℓ K Ω G) ∧
        IsLadicDefinedOverFiniteExtension ℓ (fieldMonodromyRepresentation ℓ K Ω G)) ∧
    (fieldMonodromyFunctor ℓ K Ω).Full ∧ (fieldMonodromyFunctor ℓ K Ω).Faithful ∧
    (∀ A : FiniteRepresentation.{0, u, uW} (PadicAlgCl ℓ) Gal(Ω/K),
      IsLadicContinuous ℓ A → IsLadicDefinedOverFiniteExtension ℓ A →
        ∃ G : ProEtale.LisseSheaf ℓ (Spec (.of K)),
          Nonempty (FiniteRepresentation.Equiv (fieldMonodromyRepresentation ℓ K Ω G) A)) ∧
    (∀ S : ShortComplex (ProEtale.AdicSheaf ℓ (Spec (.of K))),
      ProEtale.IsAdicLisseSheaf S.X₁ → ProEtale.IsAdicLisseSheaf S.X₂ →
        ProEtale.IsAdicLisseSheaf S.X₃ → S.ShortExact →
          Function.Injective (adicStalkMap ℓ K Ω S.f) ∧
            Function.Surjective (adicStalkMap ℓ K Ω S.g) ∧
              LinearMap.range (adicStalkMap ℓ K Ω S.f) = LinearMap.ker (adicStalkMap ℓ K Ω S.g)) ∧
    (∃ (hl : ∀ G H : ProEtale.LisseSheaf ℓ (Spec (.of K)),
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
          TensorProduct.map (lisseStalkMap ℓ K Ω f) (lisseStalkMap ℓ K Ω g) (θ G H v)) ∧
    (∀ G : ProEtale.LisseSheaf ℓ (Spec (.of K)),
      Simple G ↔ Representation.IsIrreducible (fieldMonodromy ℓ K Ω G))) ∧
  (∀ (ℓ : ℕ) [Fact ℓ.Prime] (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
      [IsNonarchimedeanLocalField K] (Ω : Type u) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
      (n : ℕ+),
    (∀ c : IrreducibleLadicClass.{u, u, uW} K Ω ℓ n, ∃ G : ProEtale.LisseSheaf ℓ (Spec (.of K)),
      Simple G ∧ ∀ A : FiniteRepresentation.{0, u, uW} (PadicAlgCl ℓ) Gal(Ω/K),
        ladicClassForget K Ω ℓ c = FiniteRepresentation.classOf A →
          Nonempty (FiniteRepresentation.Equiv (fieldMonodromyRepresentation ℓ K Ω G) A)) ∧
    ∀ G : ProEtale.LisseSheaf ℓ (Spec (.of K)), Simple G →
      (fieldMonodromyRepresentation ℓ K Ω G).rank = n →
        ∃ c : IrreducibleLadicClass.{u, u, uW} K Ω ℓ n,
          ∀ A : FiniteRepresentation.{0, u, uW} (PadicAlgCl ℓ) Gal(Ω/K),
            ladicClassForget K Ω ℓ c = FiniteRepresentation.classOf A →
              Nonempty (FiniteRepresentation.Equiv (fieldMonodromyRepresentation ℓ K Ω G) A))

end Langlands.Henniart.Laumon
