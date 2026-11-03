import Langlands.GroupScheme.SplitComponent.RankBound

/-! # The largest central lattice torus

Over a field, for a group functor corepresented by an algebra of finite type, there is a central
homomorphism `j` from a lattice torus, with surjective classifying map, through which every
central homomorphism from a lattice torus of finite rank factors. It comes from a central
homomorphism whose image lattice has maximal rank: the product of such a homomorphism with any
other central one has an image lattice projecting onto the first, with the same rank.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme.SplitComponent

open Corepresented.LinearEmbedding

section Lattice

variable {R : CommRingCat.{u}}

/-- The algebra map `R[Λ] → R[Λ']` induced by a lattice homomorphism. -/
abbrev lmap {Λ Λ' : Type u} [AddCommGroup Λ] [AddCommGroup Λ'] (l : Λ →+ Λ') :
    latticeAlgebra R Λ ⟶ latticeAlgebra R Λ' :=
  classify (latticeCorep R Λ') (latticeCorep R Λ) (latticeMap l)

theorem lmap_single {Λ Λ' : Type u} [AddCommGroup Λ] [AddCommGroup Λ'] (l : Λ →+ Λ') (m : Λ) :
    (lmap (R := R) l).hom (AddMonoidAlgebra.single m 1) = AddMonoidAlgebra.single (l m) 1 :=
  classify_latticeMap_single l m

theorem lmap_comp {Λ Λ' Λ'' : Type u} [AddCommGroup Λ] [AddCommGroup Λ'] [AddCommGroup Λ'']
    (l : Λ →+ Λ') (l' : Λ' →+ Λ'') : lmap (R := R) l ≫ lmap l' = lmap (l'.comp l) :=
  latticeHom_ext fun m => by
    change (lmap (R := R) l').hom ((lmap (R := R) l).hom _) = _
    rw [lmap_single, lmap_single, lmap_single]
    rfl

theorem lmap_id {Λ : Type u} [AddCommGroup Λ] : lmap (R := R) (AddMonoidHom.id Λ) = 𝟙 _ :=
  latticeHom_ext fun m => by
    rw [lmap_single]
    rfl

theorem latticeMap_comp {A B C : Type u} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (l : A →+ B) (l' : C →+ A) :
    latticeMap (R := R) l ≫ latticeMap l' = latticeMap (l.comp l') := rfl

end Lattice

section Product

variable {R : CommRingCat.{u}} {F F' : CommAlgCat.{u} R ⥤ GrpCat.{u}}

/-- The trivial natural homomorphism. -/
def trivialNat : F ⟶ F' where
  app S := GrpCat.ofHom 1
  naturality S T g := by
    ext x
    change (1 : F'.obj T) = F'.map g 1
    exact (map_one _).symm

theorem isCentralNat_trivialNat : IsCentralNat (trivialNat : F ⟶ F') :=
  fun _ _ y => Commute.one_left y

/-- The pointwise product of two natural homomorphisms, the second being central. -/
def mulNat (β₀ β : F ⟶ F') (hβ : IsCentralNat β) : F ⟶ F' where
  app S := GrpCat.ofHom (MonoidHom.mk' (fun x => β₀.app S x * β.app S x) fun x y => by
    change β₀.app S (x * y) * β.app S (x * y) = β₀.app S x * β.app S x * (β₀.app S y * β.app S y)
    rw [map_mul, map_mul, mul_assoc, mul_assoc, ← mul_assoc (β₀.app S y), ← mul_assoc (β.app S x),
      (hβ S x (β₀.app S y)).eq])
  naturality S T g := by
    ext x
    change β₀.app T (F.map g x) * β.app T (F.map g x) = F'.map g (β₀.app S x * β.app S x)
    rw [map_mul]
    exact congrArg₂ (· * ·) (ConcreteCategory.congr_hom (β₀.naturality g) x)
      (ConcreteCategory.congr_hom (β.naturality g) x)

theorem mulNat_app (β₀ β : F ⟶ F') (hβ : IsCentralNat β) (S : CommAlgCat.{u} R) (x : F.obj S) :
    (mulNat β₀ β hβ).app S x = β₀.app S x * β.app S x := rfl

theorem IsCentralNat.mulNat {β₀ β : F ⟶ F'} (hβ₀ : IsCentralNat β₀) (hβ : IsCentralNat β) :
    IsCentralNat (mulNat β₀ β hβ) :=
  fun S x y => (hβ₀ S x y).mul_left (hβ S x y)

variable {Λ₀ Λ : Type u} [AddCommGroup Λ₀] [AddCommGroup Λ]

/-- Restricting the product along the first factor gives the first homomorphism. -/
theorem latticeMap_fst_mulNat (α₀ : latticeFunctor R Λ₀ ⟶ F') (α : latticeFunctor R Λ ⟶ F')
    (hα : IsCentralNat α) :
    latticeMap (AddMonoidHom.fst Λ₀ Λ) ≫
        mulNat (latticeMap (AddMonoidHom.inl Λ₀ Λ) ≫ α₀) (latticeMap (AddMonoidHom.inr Λ₀ Λ) ≫ α)
          (hα.comp _) = α₀ := by
  ext S χ
  have h2 : (latticeMap (R := R) (AddMonoidHom.inr Λ₀ Λ)).app S
      ((latticeMap (R := R) (AddMonoidHom.fst Λ₀ Λ)).app S χ) = 1 := by
    apply MonoidHom.ext
    intro m
    exact map_one (asChar χ)
  change α₀.app S χ * α.app S ((latticeMap (R := R) (AddMonoidHom.inr Λ₀ Λ)).app S
      ((latticeMap (R := R) (AddMonoidHom.fst Λ₀ Λ)).app S χ)) = α₀.app S χ
  rw [h2, map_one, mul_one]

/-- Restricting the product along the second factor gives the second homomorphism. -/
theorem latticeMap_snd_mulNat (α₀ : latticeFunctor R Λ₀ ⟶ F') (α : latticeFunctor R Λ ⟶ F')
    (hα : IsCentralNat α) :
    latticeMap (AddMonoidHom.snd Λ₀ Λ) ≫
        mulNat (latticeMap (AddMonoidHom.inl Λ₀ Λ) ≫ α₀) (latticeMap (AddMonoidHom.inr Λ₀ Λ) ≫ α)
          (hα.comp _) = α := by
  ext S χ
  have h1 : (latticeMap (R := R) (AddMonoidHom.inl Λ₀ Λ)).app S
      ((latticeMap (R := R) (AddMonoidHom.snd Λ₀ Λ)).app S χ) = 1 := by
    apply MonoidHom.ext
    intro m
    exact map_one (asChar χ)
  change α₀.app S ((latticeMap (R := R) (AddMonoidHom.inl Λ₀ Λ)).app S
      ((latticeMap (R := R) (AddMonoidHom.snd Λ₀ Λ)).app S χ)) * α.app S χ = α.app S χ
  rw [h1, map_one, one_mul]

end Product

section Field

variable {k : Type u} [Field k]
  {F' : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}} {B' : CommAlgCat.{u} (CommRingCat.of k)}
  (d : (F' ⋙ forget GrpCat).CorepresentableBy B')

/-- The image lattice of a restriction is the image of the image lattice. -/
theorem imageSubgroup_latticeMap_comp {Λ Λ' : Type u} [AddCommGroup Λ] [AddCommGroup Λ']
    (l : Λ →+ Λ') (α : latticeFunctor (CommRingCat.of k) Λ ⟶ F') :
    imageSubgroup d (latticeMap l ≫ α) = (imageSubgroup d α).map l := by
  classical
  have hψ : ∀ h, (classify (latticeCorep _ Λ') d (latticeMap l ≫ α)).hom h =
      (lmap (R := CommRingCat.of k) l).hom ((classify (latticeCorep _ Λ) d α).hom h) := by
    intro h
    rw [classify_comp (latticeCorep _ Λ') (latticeCorep _ Λ) d]
    rfl
  ext n
  rw [AddSubgroup.mem_map, mem_imageSubgroup]
  constructor
  · intro hn
    obtain ⟨h, hh⟩ := (AlgHom.mem_range _).mp hn
    rw [hψ, DFunLike.congr_fun (classify_latticeMap_hom (R := CommRingCat.of k) l),
      AddMonoidAlgebra.mapDomainAlgHom_apply] at hh
    have hmem : n ∈ (AddMonoidAlgebra.mapDomain l
        ((classify (latticeCorep _ Λ) d α).hom h)).coeff.support := by
      rw [hh]
      simp
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hmem)
    exact ⟨m, (mem_range_iff d α _).mp (AlgHom.mem_range_self _ h) m hm, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨h, hh⟩ := (AlgHom.mem_range _).mp ((mem_imageSubgroup d).mp hm)
    refine (AlgHom.mem_range _).mpr ⟨h, ?_⟩
    rw [hψ, hh, lmap_single]

/-- The ranks of image lattices of central homomorphisms from lattice tori of finite rank. -/
def RankRealized (r : ℕ) : Prop :=
  ∃ (Λ : Type u) (_ : AddCommGroup Λ) (_ : Module.Free ℤ Λ) (_ : Module.Finite ℤ Λ)
    (α : latticeFunctor (CommRingCat.of k) Λ ⟶ F'),
    IsCentralNat α ∧ Module.finrank ℤ (imageSubgroup d α).toIntSubmodule = r

/-- A central homomorphism from a lattice torus whose image lattice has maximal rank. -/
theorem exists_maxRank (hfin : Algebra.FiniteType (CommRingCat.of k) B') :
    ∃ (Λ₀ : Type u) (_ : AddCommGroup Λ₀) (_ : Module.Free ℤ Λ₀) (_ : Module.Finite ℤ Λ₀)
      (α₀ : latticeFunctor (CommRingCat.of k) Λ₀ ⟶ F'), IsCentralNat α₀ ∧
      ∀ (Λ : Type u) [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
        (α : latticeFunctor (CommRingCat.of k) Λ ⟶ F'), IsCentralNat α →
        Module.finrank ℤ (imageSubgroup d α).toIntSubmodule ≤
          Module.finrank ℤ (imageSubgroup d α₀).toIntSubmodule := by
  classical
  obtain ⟨N, hN⟩ := exists_rank_bound d hfin
  have hreal : RankRealized d (Module.finrank ℤ (imageSubgroup d
      (trivialNat : latticeFunctor (CommRingCat.of k) PUnit.{u + 1} ⟶ F')).toIntSubmodule) :=
    ⟨PUnit, inferInstance, inferInstance, inferInstance, trivialNat, isCentralNat_trivialNat, rfl⟩
  obtain ⟨Λ₀, i₁, i₂, i₃, α₀, hc, hr⟩ :=
    Nat.findGreatest_spec (P := RankRealized d) (hN _ _) hreal
  refine ⟨Λ₀, i₁, i₂, i₃, α₀, hc, fun Λ _ _ _ α hα => ?_⟩
  rw [hr]
  exact Nat.le_findGreatest (hN Λ α) ⟨Λ, inferInstance, inferInstance, inferInstance, α, hα, rfl⟩

omit [Field k] in
/-- A submodule of a free `ℤ`-module of finite rank is free of finite rank. -/
theorem free_finite_submodule {Λ : Type u} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    (N : Submodule ℤ Λ) : Module.Free ℤ N ∧ Module.Finite ℤ N :=
  let b := (Submodule.basisOfPid (Module.finBasis ℤ Λ) N).2
  ⟨Module.Free.of_basis b, Module.Finite.of_basis b⟩

/-- **The largest central lattice torus.** For a group functor corepresented by an algebra of
finite type over a field, there is a central homomorphism `j` from a lattice torus of finite rank,
with surjective classifying map, through which every central homomorphism from a lattice torus
of finite rank factors. -/
theorem exists_universal (hfin : Algebra.FiniteType (CommRingCat.of k) B') :
    ∃ (J : Type u) (_ : Finite J)
      (j : latticeFunctor (CommRingCat.of k) (FreeAbelianGroup J) ⟶ F'),
      IsCentralNat j ∧ Function.Surjective (classify (latticeCorep _ _) d j).hom ∧
      ∀ (Λ : Type u) [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
        (α : latticeFunctor (CommRingCat.of k) Λ ⟶ F'), IsCentralNat α →
        ∃ l : FreeAbelianGroup J →+ Λ, latticeMap l ≫ j = α := by
  classical
  obtain ⟨Λ₀, _, _, _, α₀, hc₀, hmax⟩ := exists_maxRank d hfin
  set M₀ := imageSubgroup d α₀ with hM₀
  obtain ⟨n, b⟩ := Submodule.basisOfPid (Module.finBasis ℤ Λ₀) M₀.toIntSubmodule
  let J := ULift.{u} (Fin n)
  let E : FreeAbelianGroup J ≃+ M₀ :=
    ((FreeAbelianGroup.equivFinsupp J).trans (Finsupp.domCongr Equiv.ulift)).trans
      (b.repr.symm.toAddEquiv.trans
        { toFun := fun x => ⟨x.1, x.2⟩
          invFun := fun x => ⟨x.1, x.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl })
  refine ⟨J, inferInstance, latticeMap E.symm.toAddMonoidHom ≫ imageHom d α₀,
    (hc₀.imageHom d).comp _, ?_, ?_⟩
  · rw [classify_comp (latticeCorep _ _) (latticeCorep _ M₀) d, classify_imageHom]
    have hEE : E.symm.toAddMonoidHom.comp E.toAddMonoidHom = AddMonoidHom.id _ := by
      ext x
      simp
    have hl : Function.Surjective (lmap (R := CommRingCat.of k) E.symm.toAddMonoidHom).hom := by
      intro y
      refine ⟨(lmap (R := CommRingCat.of k) E.toAddMonoidHom).hom y, ?_⟩
      have := congrArg (fun q : latticeAlgebra (CommRingCat.of k) (FreeAbelianGroup J) ⟶
          latticeAlgebra (CommRingCat.of k) (FreeAbelianGroup J) => q.hom y)
        (lmap_comp (R := CommRingCat.of k) E.toAddMonoidHom E.symm.toAddMonoidHom)
      rw [hEE, lmap_id] at this
      exact this
    intro y
    obtain ⟨z, rfl⟩ := hl y
    obtain ⟨h, rfl⟩ := imageClassify_surjective d α₀ z
    exact ⟨h, rfl⟩
  · intro Λ _ _ _ α hα
    set α' := mulNat (latticeMap (AddMonoidHom.inl Λ₀ Λ) ≫ α₀)
      (latticeMap (AddMonoidHom.inr Λ₀ Λ) ≫ α) (hα.comp _) with hα'
    have hc' : IsCentralNat α' := (hc₀.comp _).mulNat (hα.comp _)
    have h₁ : latticeMap (AddMonoidHom.fst Λ₀ Λ) ≫ α' = α₀ := latticeMap_fst_mulNat α₀ α hα
    have h₂ : latticeMap (AddMonoidHom.snd Λ₀ Λ) ≫ α' = α := latticeMap_snd_mulNat α₀ α hα
    set M' := imageSubgroup d α'
    have hM : M₀ = M'.map (AddMonoidHom.fst Λ₀ Λ) := by
      rw [hM₀, ← h₁, imageSubgroup_latticeMap_comp]
    have hmaps : ∀ x ∈ M', x.1 ∈ M₀ := fun x hx => by
      rw [hM]
      exact AddSubgroup.mem_map_of_mem _ hx
    let ρ : M' →+ M₀ :=
      { toFun := fun x => ⟨x.1.1, hmaps x.1 x.2⟩
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hρs : Function.Surjective ρ := by
      rintro ⟨y, hy⟩
      rw [hM] at hy
      obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.mp hy
      exact ⟨⟨x, hx⟩, rfl⟩
    obtain ⟨_, _⟩ := free_finite_submodule M'.toIntSubmodule
    obtain ⟨_, _⟩ := free_finite_submodule M₀.toIntSubmodule
    let ρL : M'.toIntSubmodule →ₗ[ℤ] M₀.toIntSubmodule :=
      { toFun := fun x => ⟨x.1.1, hmaps x.1 x.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hρLs : Function.Surjective ρL := by
      rintro ⟨y, hy⟩
      obtain ⟨x, hx⟩ := hρs ⟨y, hy⟩
      exact ⟨⟨x.1, x.2⟩, congrArg (fun z : M₀ => (⟨z.1, z.2⟩ : M₀.toIntSubmodule)) hx⟩
    have hrank : Module.finrank ℤ M'.toIntSubmodule ≤ Module.finrank ℤ M₀.toIntSubmodule :=
      hmax _ α' hc'
    have hrank' : Module.finrank ℤ M₀.toIntSubmodule ≤ Module.finrank ℤ M'.toIntSubmodule := by
      have := LinearMap.finrank_range_le ρL
      rwa [LinearMap.range_eq_top.mpr hρLs, finrank_top] at this
    let e := LinearEquiv.ofFinrankEq M₀.toIntSubmodule M'.toIntSubmodule
      (le_antisymm hrank' hrank)
    have hinjL : Function.Injective ρL := by
      have := OrzechProperty.injective_of_surjective_endomorphism (e.toLinearMap ∘ₗ ρL)
        (e.surjective.comp hρLs)
      intro x y hxy
      exact this (by simp [hxy])
    have hρi : Function.Injective ρ := by
      intro x y hxy
      have : ρL ⟨x.1, x.2⟩ = ρL ⟨y.1, y.2⟩ :=
        congrArg (fun z : M₀ => (⟨z.1, z.2⟩ : M₀.toIntSubmodule)) hxy
      exact Subtype.ext (congrArg Subtype.val (hinjL this))
    let ρe : M' ≃+ M₀ := AddEquiv.ofBijective ρ ⟨hρi, hρs⟩
    let l : M₀ →+ Λ := (AddMonoidHom.snd Λ₀ Λ).comp (M'.subtype.comp ρe.symm.toAddMonoidHom)
    refine ⟨l.comp E.toAddMonoidHom, ?_⟩
    rw [← Category.assoc, latticeMap_comp]
    have hlE : (l.comp E.toAddMonoidHom).comp E.symm.toAddMonoidHom = l := by
      ext x
      simp
    rw [hlE]
    apply nat_ext (latticeCorep _ Λ) d
    rw [classify_comp (latticeCorep _ Λ) (latticeCorep _ M₀) d, classify_imageHom]
    have hfst : M₀.subtype.comp ρ = (AddMonoidHom.fst Λ₀ Λ).comp M'.subtype := rfl
    have hl : l.comp ρ = (AddMonoidHom.snd Λ₀ Λ).comp M'.subtype := by
      ext x
      change (ρe.symm (ρe x)).1.2 = x.1.2
      rw [AddEquiv.symm_apply_apply]
    have hα₀ : classify (latticeCorep _ Λ₀) d α₀ =
        classify (latticeCorep _ (Λ₀ × Λ)) d α' ≫ lmap (AddMonoidHom.fst Λ₀ Λ) := by
      rw [← h₁, classify_comp (latticeCorep _ Λ₀) (latticeCorep _ (Λ₀ × Λ)) d]
    have hα : classify (latticeCorep _ Λ) d α =
        classify (latticeCorep _ (Λ₀ × Λ)) d α' ≫ lmap (AddMonoidHom.snd Λ₀ Λ) := by
      rw [← h₂, classify_comp (latticeCorep _ Λ) (latticeCorep _ (Λ₀ × Λ)) d]
    have k₁ : imageClassify d α₀ = imageClassify d α' ≫ lmap ρ := by
      apply cancel_injective (incl_injective M₀)
      rw [imageClassify_comp_incl, hα₀, ← imageClassify_comp_incl d α', Category.assoc,
        Category.assoc, lmap_comp, lmap_comp, hfst]
    rw [k₁, Category.assoc, lmap_comp, hl, hα, ← imageClassify_comp_incl d α', Category.assoc,
      lmap_comp]

end Field

end Langlands.GroupScheme.SplitComponent
