/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module



import Mathlib.AlgebraicGeometry.AlgClosed.Basic

public import Mathlib.AlgebraicGeometry.Artinian
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance
public import WeilConjectures.AlgebraicGeometry.Sites.FiniteSupport
public import WeilConjectures.AlgebraicGeometry.Sites.LerayVanishing
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.DisjointUnion

/-!
# Étale cohomology of zero-dimensional schemes

Let `C` be a scheme of finite type over an algebraically closed field `k` with
`dim C ≤ 0`. Then `C` is a finite discrete space all of whose residue fields are
algebraically closed, and for every abelian étale sheaf `F` on `C`:

* `Hᵠ(C, F) = 0` for `q > 0`;
* the map `H⁰(C, F) ⟶ ∏_x F_{s x}` to the stalks at geometric points `s x` over the points
  `x` of `C` is an isomorphism.

The vanishing is `AlgebraicGeometry.Etale.subsingleton_H_of_isZero_upperStar` (a sheaf supported
on finitely many closed points with separably closed residue fields is acyclic). For the
degree zero statement, `F(C) = ∏_x F({x})` since the points `{x}` are open, and the pointed
open neighbourhood `({x}, s x)` is initial among the pointed étale neighbourhoods of `s x`, so
that `F({x}) = F_{s x}`: an étale scheme over the one-point scheme `{x}` with a point over `x`
has a section through that point, by topological invariance of the étale site along
`Spec κ(x) ⟶ {x}`.

## Main statements

- `AlgebraicGeometry.zero_dimensional_etale_cohomology`
  (blueprint `lemma-sheaves-finite-support-finite-morphisms--1`): the statement above.
- `AlgebraicGeometry.Etale.isIso_piLift_toPresheafFiber`: on a finite discrete scheme with
  separably closed residue fields, the sections of a sheaf are the product of its stalks.
-/

@[expose] public section

universe u u' v'

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A scheme of finite type over a field whose dimension is at most zero has finitely many
points: it is Noetherian of dimension zero, hence Artinian. -/
theorem Scheme.finite_of_topologicalKrullDim_le_zero {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    (hdim : topologicalKrullDim C ≤ 0) : Finite C := by
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace f
  have := IsLocallyArtinian.of_topologicalKrullDim_le_zero hdim
  have : IsArtinianScheme C := ⟨⟩
  infer_instance

/-- A scheme locally of finite type over a field whose dimension is at most zero is discrete:
it is locally Noetherian of dimension zero, hence locally Artinian. -/
lemma Scheme.discreteTopology_of_topologicalKrullDim_le_zero {k : Type u} [Field k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim C ≤ 0) : DiscreteTopology C := by
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have := IsLocallyArtinian.of_topologicalKrullDim_le_zero hdim
  exact (IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology.1 this).2

/-- Two field-valued points `a b : Spec Ω ⟶ V` of a scheme `V` étale over `S`, with the same
image point and the same composite to `S`, are equal if the residue field of `S` at their image
is separably closed: the residue field extension at that point is then trivial. -/
theorem Scheme.eq_of_comp_eq_of_isSepClosed {V S : Scheme.{u}} (p : V ⟶ S) [Etale p]
    {Ω : Type u} [Field Ω] {a b : Spec (.of Ω) ⟶ V} (hab : a ≫ p = b ≫ p)
    (hpt : a default = b default) (hsep : IsSepClosed (S.residueField (p (a default)))) :
    a = b := by
  obtain ⟨⟨y, α⟩, rfl⟩ := (Scheme.SpecToEquivOfField Ω V).symm.surjective a
  obtain ⟨⟨y', β⟩, rfl⟩ := (Scheme.SpecToEquivOfField Ω V).symm.surjective b
  rw [show ((SpecToEquivOfField Ω V).symm ⟨y, α⟩) default = y by
    simp [SpecToEquivOfField]] at hsep
  simp only [SpecToEquivOfField, Equiv.coe_fn_symm_mk, Scheme.Hom.comp_apply,
    Scheme.fromSpecResidueField_apply] at hpt hab ⊢
  subst hpt
  rw [Category.assoc, Category.assoc, ← p.SpecMap_residueFieldMap_fromSpecResidueField,
    ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, cancel_mono,
    Spec.map_inj] at hab
  algebraize [(p.residueFieldMap y).hom]
  have hs := IsSepClosed.algebraMap_surjective (S.residueField (p y)) (V.residueField y)
  have : α = β := by
    ext z
    obtain ⟨w, rfl⟩ := hs z
    exact congr($hab w)
  rw [this]

/-- Let `U` be a scheme with a single point, whose residue field is separably closed, and
`p : V ⟶ U` étale. Every field-valued point `v` of `V` lies on a section of `p`. The section
is obtained over `Spec κ`, `κ` the residue field of `U`, and lifted to `U` by topological
invariance of the étale site along the universal homeomorphism `Spec κ ⟶ U`. -/
theorem Scheme.exists_section_of_etale_of_subsingleton {U V : Scheme.{u}} [Subsingleton U]
    (hsep : ∀ x : U, IsSepClosed (U.residueField x)) (p : V ⟶ U) [Etale p]
    {Ω : Type u} [Field Ω] (v : Spec (.of Ω) ⟶ V) :
    ∃ σ : U ⟶ V, σ ≫ p = 𝟙 U ∧ (v ≫ p) ≫ σ = v := by
  obtain ⟨⟨x, a⟩, hu⟩ := (Scheme.SpecToEquivOfField Ω U).symm.surjective (v ≫ p)
  change Spec.map a ≫ U.fromSpecResidueField x = v ≫ p at hu
  have := hsep x
  let i := U.fromSpecResidueField x
  have : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.1 (by
    rw [show ({x} : Set U) = Set.univ from Set.eq_univ_of_forall fun y ↦ Subsingleton.elim y x]
    exact isClosed_univ)
  have : Surjective i := ⟨fun y ↦ ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩⟩
  -- a section `l` of the base change of `p` to `Spec κ` through the point given by `v`
  let w : Spec (.of Ω) ⟶ pullback p i := pullback.lift v (Spec.map a) hu.symm
  obtain ⟨l, hl, hly⟩ := exists_fac_of_etale_of_isSepClosed (Ω := U.residueField x)
    (pullback.snd p i) (𝟙 (Spec (U.residueField x))) (w default) (Subsingleton.elim _ _)
  let φ : i.Etale.obj (Etale.mk (𝟙 U)) ⟶ i.Etale.obj (Etale.mk p) :=
    MorphismProperty.Over.homMk (pullback.snd (𝟙 U) i ≫ l) (by
      change (pullback.snd (𝟙 U) i ≫ l) ≫ pullback.snd p i = pullback.snd (𝟙 U) i
      rw [Category.assoc, hl, Category.comp_id])
  -- its lift to `U`
  let σ₀ := i.Etale.preimage φ
  have hσ : σ₀.left ≫ p = 𝟙 U := MorphismProperty.Over.w σ₀
  refine ⟨σ₀.left, hσ, ?_⟩
  refine Scheme.eq_of_comp_eq_of_isSepClosed p (by rw [Category.assoc, hσ, Category.comp_id])
    ?_ (hsep _)
  let z : ↥(pullback (𝟙 U) i) := (pullback.lift i (𝟙 _) (by simp) :
    Spec (U.residueField x) ⟶ pullback (𝟙 U) i) default
  have h₁ : φ.left ≫ pullback.fst p i = pullback.fst (𝟙 U) i ≫ σ₀.left := by
    have h := i.etale_map_left_comp_fst σ₀
    rw [Functor.map_preimage] at h
    exact h
  have h₂ : (pullback.fst (𝟙 U) i ≫ σ₀.left) z = v default := by
    rw [← h₁]
    change (pullback.fst p i) (l (pullback.snd (𝟙 U) i z)) = v default
    rw [Subsingleton.elim (pullback.snd (𝟙 U) i z) default, hly, ← Scheme.Hom.comp_apply,
      pullback.lift_fst]
  rw [← h₂]
  exact congrArg σ₀.left.base (Subsingleton.elim (α := U) _ _)

section OnePoint

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
  (U : X.Opens) (hs : Set.range s ⊆ (U : Set X))

/-- The geometric point `s` of `X`, lifted to an open subscheme `U` containing its image. -/
noncomputable def Scheme.pointSmallEtaleFiberObjOpens :
    (pointSmallEtale s).fiber.obj (Etale.mk U.ι) :=
  Over.homMk (U := Over.mk s) (V := Over.mk U.ι)
    (IsOpenImmersion.lift U.ι s ((Scheme.Opens.range_ι U).symm ▸ hs))
    (IsOpenImmersion.lift_fac _ _ _)

lemma Scheme.pointSmallEtaleFiberObjOpens_left_ι :
    (Scheme.pointSmallEtaleFiberObjOpens s U hs).left ≫ U.ι = s :=
  IsOpenImmersion.lift_fac _ _ _

/-- The open subscheme `U` of `X`, pointed by the geometric point `s`, as a pointed étale
neighbourhood of `s`. -/
noncomputable abbrev Scheme.pointSmallEtaleElementsOpens : (pointSmallEtale s).fiber.Elements :=
  (pointSmallEtale s).fiber.elementsMk (Etale.mk U.ι) (Scheme.pointSmallEtaleFiberObjOpens s U hs)

/-- If `U` has a single point, with separably closed residue field, then `(U, s)` maps to every
pointed étale neighbourhood of `s`, by
`AlgebraicGeometry.Scheme.exists_section_of_etale_of_subsingleton` applied to its base change
to `U`. -/
lemma Scheme.nonempty_hom_pointSmallEtaleElementsOpens (hU : (U : Set X).Subsingleton)
    (hsep : ∀ x ∈ U, IsSepClosed (X.residueField x)) (c : (pointSmallEtale s).fiber.Elements) :
    Nonempty (Scheme.pointSmallEtaleElementsOpens s U hs ⟶ c) := by
  obtain @⟨V, v⟩ := c
  have : Subsingleton U.toScheme := hU.coe_sort
  have hsep' (y : U.toScheme) : IsSepClosed (U.toScheme.residueField y) :=
    have := hsep (U.ι y) (by simp)
    IsSepClosed.of_ringEquiv (asIso (U.ι.residueFieldMap y)).commRingCatIsoToRingEquiv
  set s' := (Scheme.pointSmallEtaleFiberObjOpens s U hs).left
  have hs' : s' ≫ U.ι = s := Scheme.pointSmallEtaleFiberObjOpens_left_ι s U hs
  have : Etale V.hom := V.prop
  have hv : v.left ≫ V.hom = s := Over.w v
  obtain ⟨σ, hσ, hσv⟩ := Scheme.exists_section_of_etale_of_subsingleton hsep'
    (pullback.snd V.hom U.ι) (pullback.lift v.left s' (by rw [hv, hs']))
  rw [pullback.lift_snd] at hσv
  refine ⟨Functor.Elements.homMk
    (MorphismProperty.Over.homMk (σ ≫ pullback.fst V.hom U.ι) ?_) ?_⟩
  · change (σ ≫ pullback.fst V.hom U.ι) ≫ V.hom = U.ι
    rw [Category.assoc, pullback.condition, ← Category.assoc, hσ, Category.id_comp]
  · refine Over.OverMorphism.ext ?_
    change s' ≫ σ ≫ pullback.fst V.hom U.ι = v.left
    rw [← Category.assoc, hσv, pullback.lift_fst]

/-- If `U` has a single point, there is at most one morphism from `(U, s)` to a pointed étale
neighbourhood of `s`: two such morphisms agree on an open subset of `U` containing the image of
`s` (`AlgebraicGeometry.FormallyUnramified.eqLocus`), that is, on all of `U`. -/
lemma Scheme.subsingleton_hom_pointSmallEtaleElementsOpens (hU : (U : Set X).Subsingleton)
    (c : (pointSmallEtale s).fiber.Elements) :
    Subsingleton (Scheme.pointSmallEtaleElementsOpens s U hs ⟶ c) := by
  obtain @⟨V, v⟩ := c
  have : Subsingleton U.toScheme := hU.coe_sort
  have : Etale V.hom := V.prop
  refine ⟨fun g g' ↦ Functor.Elements.hom_ext (MorphismProperty.Over.Hom.ext ?_)⟩
  have hab : g.hom.left ≫ V.hom = g'.hom.left ≫ V.hom := by
    rw [MorphismProperty.Over.w g.hom, MorphismProperty.Over.w g'.hom]
  set s' := (Scheme.pointSmallEtaleFiberObjOpens s U hs).left
  have hg (g : Scheme.pointSmallEtaleElementsOpens s U hs ⟶
      (pointSmallEtale s).fiber.elementsMk V v) :
      s' ≫ g.hom.left = v.left :=
    congrArg (fun t ↦ t.left) g.map_val
  have hmem := FormallyUnramified.range_subset_eqLocus V.hom _ _ hab s' (by rw [hg, hg])
  let E := FormallyUnramified.eqLocus V.hom _ _ hab
  have : IsIso E.ι := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    exact ⟨inferInstance, ⟨fun y ↦ ⟨⟨_, hmem ⟨(default : Spec (.of Ω)), rfl⟩⟩,
      Subsingleton.elim (α := ↥(U : Scheme.{u})) _ _⟩⟩⟩
  exact (cancel_epi E.ι).1 (FormallyUnramified.eqLocus_ι_comp_eq V.hom _ _ hab)

/-- If `U` has a single point, with separably closed residue field, then `(U, s)` is an initial
pointed étale neighbourhood of `s`. -/
noncomputable def Scheme.isInitialPointSmallEtaleElementsOpens (hU : (U : Set X).Subsingleton)
    (hsep : ∀ x ∈ U, IsSepClosed (X.residueField x)) :
    IsInitial (Scheme.pointSmallEtaleElementsOpens s U hs) :=
  IsInitial.ofUniqueHom
    (fun c ↦ (Scheme.nonempty_hom_pointSmallEtaleElementsOpens s U hs hU hsep c).some)
    (fun c _ ↦ (Scheme.subsingleton_hom_pointSmallEtaleElementsOpens s U hs hU c).elim _ _)

/-- If `U` has a single point, with separably closed residue field, then the stalk of a presheaf
`P` at `s` is `P(U)`: the canonical map `P(U) ⟶ P_s` is an isomorphism. -/
lemma Scheme.isIso_toPresheafFiber_pointSmallEtaleFiberObjOpens {A : Type u'} [Category.{v'} A]
    [HasColimitsOfSize.{u, u} A] (hU : (U : Set X).Subsingleton)
    (hsep : ∀ x ∈ U, IsSepClosed (X.residueField x)) (P : X.Etaleᵒᵖ ⥤ A) :
    IsIso ((pointSmallEtale s).toPresheafFiber (Etale.mk U.ι)
      (Scheme.pointSmallEtaleFiberObjOpens s U hs) P) := by
  unfold GrothendieckTopology.Point.toPresheafFiber
  exact @isIso_ι_of_isTerminal _ _ _ _ _
    (Scheme.isInitialPointSmallEtaleElementsOpens s U hs hU hsep).op _
    (HasColimitsOfShape.has_colimit _)

end OnePoint

/-- **Sections over a finite discrete scheme.** Let `X` be a finite discrete scheme whose
residue fields are separably closed, and for every point `x` let `s x` be a geometric point of
`X` at `x`. For every sheaf `P` on the small étale site of `X`, the map
`P(X) ⟶ ∏_x P_{s x}` to the stalks is an isomorphism: `P(X) = ∏_x P({x})` as the `{x}` form
a disjoint open cover, and `P({x}) = P_{s x}`
(`AlgebraicGeometry.Scheme.isIso_toPresheafFiber_pointSmallEtaleFiberObjOpens`). -/
theorem Etale.isIso_piLift_toPresheafFiber {X : Scheme.{u}} [Finite X] [DiscreteTopology X]
    (hsep : ∀ x : X, IsSepClosed (X.residueField x))
    (Ω : X → Type u) [∀ x, Field (Ω x)] [∀ x, IsSepClosed (Ω x)]
    (s : ∀ x : X, Spec (.of (Ω x)) ⟶ X) (hs : ∀ x : X, (s x).base.hom default = x)
    {A : Type u'} [Category.{u + 1} A] [HasColimitsOfSize.{u, u} A] [HasLimits A]
    (P : Sheaf X.smallEtaleTopology A) :
    IsIso (Pi.lift fun x : X ↦ (Scheme.pointSmallEtale (s x)).toPresheafFiber
      (Scheme.Etale.mk (𝟙 X)) (Over.homMk (s x) (Category.comp_id (s x))) P.obj) := by
  let U (x : X) : X.Opens := ⟨{x}, isOpen_discrete _⟩
  have hsU (x : X) : Set.range (s x) ⊆ (U x : Set X) := by
    rintro _ ⟨y, rfl⟩
    rw [Subsingleton.elim y default]
    exact hs x
  let i (x : X) : Scheme.Etale.mk (U x).ι ⟶ Scheme.Etale.mk (𝟙 X) :=
    MorphismProperty.Over.homMk (U x).ι (Category.comp_id _)
  have : ∀ x, IsOpenImmersion (i x).left := fun x ↦ inferInstanceAs (IsOpenImmersion (U x).ι)
  -- the global sections are the product of the sections over the points
  have hdisj : Pairwise fun x y ↦
      Disjoint (Set.range (i x).left.base) (Set.range (i y).left.base) := fun x y hxy ↦ by
    change Disjoint (Set.range (U x).ι) (Set.range (U y).ι)
    rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    simpa [U] using hxy
  have hcov : ⋃ x, Set.range (i x).left.base = Set.univ := by
    refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ⟨x, ?_⟩
    change x ∈ Set.range (U x).ι
    rw [Scheme.Opens.range_ι]
    rfl
  have h {a : A} (t : ∀ x, a ⟶ P.obj.obj (op (Scheme.Etale.mk (U x).ι))) :=
    Scheme.Etale.existsUnique_of_pairwise_disjoint P _ i hdisj hcov t
  let c : Fan fun x ↦ P.obj.obj (op (Scheme.Etale.mk (U x).ι)) :=
    Fan.mk (P.obj.obj (op (Scheme.Etale.mk (𝟙 X)))) fun x ↦ P.obj.map (i x).op
  have hc : IsLimit c := Fan.IsLimit.mk _ (fun t ↦ (h t.proj).exists.choose)
    (fun t x ↦ (h t.proj).exists.choose_spec x)
    (fun t m hm ↦ (h t.proj).unique hm (h t.proj).exists.choose_spec)
  have : IsIso (Pi.lift c.proj) := by
    have : Pi.lift c.proj = (hc.conePointUniqueUpToIso (limit.isLimit _)).hom := by
      ext x
      simp [Fan.proj]
    rw [this]
    infer_instance
  -- the stalk at `s x` is the group of sections over the point `x`
  have (x : X) := Scheme.isIso_toPresheafFiber_pointSmallEtaleFiberObjOpens (s x) (U x) (hsU x)
    Set.subsingleton_singleton (fun y _ ↦ hsep y) P.obj
  have h : (Pi.lift fun x : X ↦ (Scheme.pointSmallEtale (s x)).toPresheafFiber
      (Scheme.Etale.mk (𝟙 X)) (Over.homMk (s x) (Category.comp_id (s x))) P.obj) =
      Pi.lift c.proj ≫ Limits.Pi.map fun x ↦ (Scheme.pointSmallEtale (s x)).toPresheafFiber
        (Scheme.Etale.mk (U x).ι) (Scheme.pointSmallEtaleFiberObjOpens (s x) (U x) (hsU x))
          P.obj := by
    ext x
    simp only [Pi.lift_comp_π, Category.assoc, Pi.map_π, Pi.lift_comp_π_assoc]
    change _ = P.obj.map (i x).op ≫ _
    rw [GrothendieckTopology.Point.toPresheafFiber_w]
    congr 1
    exact Over.OverMorphism.ext
      (Scheme.pointSmallEtaleFiberObjOpens_left_ι (s x) (U x) (hsU x)).symm
  rw [h]
  infer_instance

/-- Let `C` be a scheme of finite type and of dimension at most zero over an algebraically
closed field. Every abelian étale sheaf on `C` has no cohomology in positive degrees: it is
supported on the finitely many closed points of `C`, whose residue fields are algebraically
closed (`AlgebraicGeometry.Etale.subsingleton_H_of_isZero_upperStar`). -/
lemma Etale.subsingleton_cohomology_of_topologicalKrullDim_le_zero {k : Type u} [Field k]
    [IsAlgClosed k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    [QuasiCompact f] (hdim : topologicalKrullDim C ≤ 0)
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (hq : 0 < q) :
    Subsingleton ((Etale.cohomology AddCommGrpCat.{u + 1} C q).obj
      ((DerivedCategory.singleFunctor (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
        F)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hq
  rw [zero_add]
  have := Scheme.finite_of_topologicalKrullDim_le_zero f hdim
  have := Scheme.discreteTopology_of_topologicalKrullDim_le_zero f hdim
  have : IsEmpty ((⊥ : C.Opens) : Scheme.{u}) := ⟨fun ⟨y, hy⟩ ↦ by simp at hy⟩
  have hH : Subsingleton (Sheaf.H F (n + 1)) :=
    Etale.subsingleton_H_of_isZero_upperStar ⊥ (Set.toFinite _) (fun x _ ↦ isClosed_discrete _)
      (fun x _ ↦ have := (IsAlgClosed.of_ringEquiv k _
        (residueFieldIsoBase f x (isClosed_discrete _)).commRingCatIsoToRingEquiv.symm)
        inferInstance) F (Scheme.Etale.isZero_sheaf_of_isEmpty _) n
  -- compare `Hⁿ⁺¹(C, F)` with the right derived functors of the global sections
  rw [Etale.subsingleton_H_iff_isZero_rightDerived_Γ] at hH
  have : ((sheafSections C.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op (⊤_ C.Etale))).Additive :=
    inferInstanceAs (sheafToPresheaf _ _ ⋙ (evaluation _ AddCommGrpCat.{u + 1}).obj _).Additive
  have e := (NatIso.rightDerived (Sheaf.ΓNatIsoSheafSections C.smallEtaleTopology
    AddCommGrpCat.{u + 1} terminalIsTerminal) (n + 1)).app F
  rw [← AddCommGrpCat.isZero_iff_subsingleton]
  exact hH.of_iso ((Functor.homologyRightDerivedFunctorObjSingleFunctorIso _ F (n + 1)) ≪≫ e)

/-- Let `C` be a scheme of finite type and of dimension at most zero over an algebraically
closed field, and `s x` a geometric point of `C` at every point `x`. For every abelian étale
sheaf `F` on `C` the canonical map `H⁰(C, F) ⟶ ∏_x F_{s x}` is an isomorphism
(`AlgebraicGeometry.Etale.isIso_piLift_toPresheafFiber`). -/
lemma Etale.isIso_toPresheafFiber_of_topologicalKrullDim_le_zero {k : Type u} [Field k]
    [IsAlgClosed k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    [QuasiCompact f] (hdim : topologicalKrullDim C ≤ 0)
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (Ω : C → Type u) [∀ x, Field (Ω x)] [∀ x, IsAlgClosed (Ω x)]
    (s : ∀ x : C, Spec (.of (Ω x)) ⟶ C) (hs : ∀ x : C, (s x).base.hom default = x) :
    IsIso ((Functor.homologyRightDerivedFunctorObjSingleFunctorIso
        (Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1}) F 0).hom ≫
      (Functor.rightDerivedZeroIsoSelf
        (Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1})).hom.app F ≫
      F.ΓRes (op (Scheme.Etale.mk (𝟙 C))) ≫
      Pi.lift (fun x : C ↦ (Scheme.pointSmallEtale (s x)).toPresheafFiber
        (Scheme.Etale.mk (𝟙 C)) (Over.homMk (s x) (Category.comp_id (s x))) F.obj)) := by
  have := Scheme.finite_of_topologicalKrullDim_le_zero f hdim
  have := Scheme.discreteTopology_of_topologicalKrullDim_le_zero f hdim
  -- the restriction from the global sections to the terminal object is an isomorphism
  have : IsIso (F.ΓRes (op (Scheme.Etale.mk (𝟙 C)))) :=
    (F.isLimitConeΓ.conePointUniqueUpToIso
      (limitOfDiagramInitial (Scheme.Etale.isTerminalMkId C).op F.obj)).isIso_hom
  have := Etale.isIso_piLift_toPresheafFiber (fun x ↦
    have := (IsAlgClosed.of_ringEquiv k _
        (residueFieldIsoBase f x (isClosed_discrete _)).commRingCatIsoToRingEquiv.symm)
    inferInstance) Ω s hs F
  infer_instance

/-- Blueprint `lemma-sheaves-finite-support-finite-morphisms--1`: **Cohomology of zero-dimensional
schemes.** Let `C` be a separated scheme of finite type over an algebraically closed field `k`
with `dim C ≤ 0`. Then `C` has finitely many points, and for every abelian étale sheaf `F` on
`C`, `Hᵠ(C, F) = 0` for `q > 0` while the canonical map `H⁰(C, F) ⟶ ∏_x F_{s x}` to the
stalks at geometric points `s x` over the points `x` of `C` is an isomorphism. -/
theorem zero_dimensional_etale_cohomology
    (k : Type u) [Field k] [IsAlgClosed k]
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hdim : topologicalKrullDim C ≤ 0)
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (Ω : C → Type u) [∀ x, Field (Ω x)] [∀ x, IsAlgClosed (Ω x)]
    (s : ∀ x : C, Spec (.of (Ω x)) ⟶ C)
    (hs : ∀ x : C, (s x).base.hom default = x) :
    Finite C ∧
    (∀ q : ℕ, 0 < q → Subsingleton
      ((Etale.cohomology AddCommGrpCat.{u + 1} C q).obj
        ((DerivedCategory.singleFunctor
          (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F))) ∧
      IsIso
        ((Functor.homologyRightDerivedFunctorObjSingleFunctorIso
            (CategoryTheory.Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1}) F 0).hom ≫
          (Functor.rightDerivedZeroIsoSelf
            (CategoryTheory.Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1})).hom.app F ≫
          F.ΓRes (op (Scheme.Etale.mk (𝟙 C))) ≫
          Pi.lift (fun x : C =>
            (Scheme.pointSmallEtale (s x)).toPresheafFiber
              (Scheme.Etale.mk (𝟙 C))
              (Over.homMk (s x) (Category.comp_id (s x))) F.obj)) :=
  ⟨Scheme.finite_of_topologicalKrullDim_le_zero f hdim,
    Etale.subsingleton_cohomology_of_topologicalKrullDim_le_zero f hdim F,
    Etale.isIso_toPresheafFiber_of_topologicalKrullDim_le_zero f hdim F Ω s hs⟩

end AlgebraicGeometry
