import Langlands.GroupScheme.Torus.AffineRelativeDiagonalizable
import Langlands.GroupScheme.Torus.RelativeDiagonalizableExactQuotient
import Langlands.GroupScheme.Torus.DiagonalizableAutomorphismTestLocality
import Langlands.GroupScheme.Torus.DiagonalizablePower
import Langlands.AbelianScheme.Tate.BaseChangeCoherence

/-! # Homomorphisms between diagonalizable groups over a base are locally monomial -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

/-! ### Affine homomorphisms between diagonalizable groups -/

namespace Langlands.GroupScheme.Diagonalizable

variable {R : CommRingCat.{u}} {M N : Type u} [AddCommGroup M] [AddCommGroup N]

/-- Hopf coordinates of a homomorphism `D_R(M) → D_R(N)`: a bialgebra map `R[N] → R[M]`. -/
def bialgHomOfHom (f : (groupScheme R M).toGrp ⟶ (groupScheme R N).toGrp) :
    AddMonoidAlgebra R N →ₐc[R] AddMonoidAlgebra R M :=
  (hopfSpec.fullyFaithful.preimage
    ((hopfSpecIso R M).hom ≫ f ≫ (hopfSpecIso R N).inv)).unop.hom

theorem bialgHomOfHom_hom_left (f : (groupScheme R M).toGrp ⟶ (groupScheme R N).toGrp) :
    f.hom.hom.left =
      Spec.map (CommRingCat.ofHom (bialgHomOfHom f).toAlgHom.toRingHom) := by
  have h := hopfSpec.fullyFaithful.map_preimage
    ((hopfSpecIso R M).hom ≫ f ≫ (hopfSpecIso R N).inv)
  have h' := congrArg (fun f => f.hom.hom.left) h
  change Spec.map (CommRingCat.ofHom (bialgHomOfHom f).toAlgHom.toRingHom) =
    ((hopfSpecIso R M).hom.hom.hom.left ≫ f.hom.hom.left) ≫
      (hopfSpecIso R N).inv.hom.hom.left at h'
  rw [hopfSpecIso_hom_left, hopfSpecIso_inv_left] at h'
  change Spec.map (CommRingCat.ofHom (bialgHomOfHom f).toAlgHom.toRingHom) =
    ((𝟙 (groupScheme R M).X.left) ≫ f.hom.hom.left) ≫
      𝟙 (groupScheme R N).X.left at h'
  simpa only [Category.id_comp, Category.comp_id] using h'.symm

open CommutativeAlgebra.DiagonalIsomorphismLocus in
/-- Equality in canonical scalar-extension coordinates detects equality of the
base-changed homomorphisms. -/
theorem baseChange_map_eq_restrictMap_of_scalarExtension_eq
    (f : (groupScheme R M).toGrp ⟶ (groupScheme R N).toGrp)
    (C : Type u) [CommRing C] [Algebra R C] (g : N →+ M)
    (h : (scalarExtension (R := R) (M := M) (N := N) (bialgHomOfHom f) C).toAlgHom =
      AddMonoidAlgebra.mapDomainAlgHom C C g) :
    (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R C)))).map f =
      (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R C)))).map
        (restrictMap R g) := by
  let f' : AddMonoidAlgebra R N →ₐ[R] AddMonoidAlgebra R M := (bialgHomOfHom f).toAlgHom
  let d : AddMonoidAlgebra R N →ₐ[R] AddMonoidAlgebra R M :=
    AddMonoidAlgebra.mapDomainAlgHom R R g
  have hcoord : scalarExtensionAlgHom f' C = scalarExtensionAlgHom d C := by
    rw [scalarExtensionAlgHom_mapDomain]
    exact h
  have hmap : Algebra.TensorProduct.map (AlgHom.id C C) f' =
      Algebra.TensorProduct.map (AlgHom.id C C) d := by
    apply Algebra.TensorProduct.ext'
    intro a b
    apply (AddMonoidAlgebra.scalarTensorEquiv R C (M := M)).injective
    have hh := DFunLike.congr_fun hcoord
      ((AddMonoidAlgebra.scalarTensorEquiv R C (M := N)) (a ⊗ₜ[R] b))
    simpa only [scalarExtensionAlgHom, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      AlgEquiv.symm_apply_apply,
      HopfMorphismBaseChange.scalarExtension_eq] using hh
  have he : f.hom.hom = (algSpec R).map (CommAlgCat.ofHom f').op :=
    Over.OverMorphism.ext (bialgHomOfHom_hom_left f)
  have hd : (restrictMap R g).hom.hom = (algSpec R).map (CommAlgCat.ofHom d).op :=
    Over.OverMorphism.ext (restrictMap_left R g)
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  change ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R C)))).map
      f.hom.hom).left =
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R C)))).map
      (restrictMap R g).hom.hom).left
  rw [he, hd]
  have hf := HopfMorphismBaseChange.tensorSpecIso_naturality (S := C) f'
  have hd' := HopfMorphismBaseChange.tensorSpecIso_naturality (S := C) d
  rw [hmap] at hf
  exact hf.trans hd'.symm

open CommutativeAlgebra.DiagonalIsomorphismLocus in
/-- Every prime of `R` has a principal neighborhood on which a homomorphism
`D_R(M) → D_R(N)` is induced by one character map `N →+ M`. -/
theorem exists_away_baseChange_map_eq_restrictMap [AddMonoid.FG N]
    (f : (groupScheme R M).toGrp ⟶ (groupScheme R N).toGrp)
    (p : Ideal R) [p.IsPrime] :
    ∃ (g : N →+ M) (r : R), r ∉ p ∧
      (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom
        (algebraMap R (Localization.Away r))))).map f =
      (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom
        (algebraMap R (Localization.Away r))))).map (restrictMap R g) := by
  classical
  obtain ⟨s, hs⟩ := AddMonoid.FG.fg_top (M := N)
  let F := bialgHomOfHom f
  let g : N →+ M := AddMonoidAlgebra.mapDomainOfBialgHom (scalarExtension F p.ResidueField)
  refine ⟨g, generatorCoefficientProduct F g s, ?_, ?_⟩
  · intro hp
    have hr : algebraMap R p.ResidueField (generatorCoefficientProduct F g s) = 1 := by
      simp only [generatorCoefficientProduct, map_prod]
      apply Finset.prod_eq_one
      intro n _
      exact field_character_coefficient F p.ResidueField n
    rw [Ideal.algebraMap_residueField_eq_zero.mpr hp] at hr
    exact zero_ne_one hr
  · exact baseChange_map_eq_restrictMap_of_scalarExtension_eq f _ g
      (scalarExtension_eq_mapDomain_of_isUnit F g s hs _
        (IsLocalization.Away.algebraMap_isUnit _))

end Langlands.GroupScheme.Diagonalizable

/-! ### Diagonalizable groups over an arbitrary base -/

namespace Langlands.GroupScheme.RelativeMultiplicativeType

variable {X Y : Scheme.{u}} {Λ Λ' Λ'' : Type u} [AddCommGroup Λ] [AddCommGroup Λ']
  [AddCommGroup Λ'']

/-- The base ring `ℤ` (lifted to universe `u`). -/
abbrev ZU : CommRingCat.{u} := CommRingCat.of (ULift.{u} ℤ)

/-- The points of `D_X(Λ)` over an `X`-scheme `T` are the homomorphisms `Λ → Γ(T, 𝒪_T)ˣ`. -/
def pointsEquiv (X : Scheme.{u}) (Λ : Type u) [AddCommGroup Λ] (T : Over X) :
    (T ⟶ (diagonalizable X Λ).X) ≃* (Multiplicative Λ →* (Γ(T.left, ⊤))ˣ) :=
  (baseChangePointsEquiv (Gm.toSpecZ X) (Diagonalizable.groupScheme ZU.{u} Λ).toGrp T).trans
    (Diagonalizable.characterPointsEquiv ZU.{u} Λ ((Over.map (Gm.toSpecZ X)).obj T))

theorem pointsEquiv_naturality {T T' : Over X} (a : T' ⟶ T)
    (t : T ⟶ (diagonalizable X Λ).X) (m : Λ) :
    pointsEquiv X Λ T' (a ≫ t) (.ofAdd m) =
      Units.map a.left.appTop.hom.toMonoidHom (pointsEquiv X Λ T t (.ofAdd m)) := by
  unfold pointsEquiv
  rw [MulEquiv.trans_apply, baseChangePointsEquiv_naturality]
  exact Diagonalizable.characterPointsEquiv_naturality ZU.{u} Λ _ _ m

theorem pointsEquiv_comp {T T' : Over X} (a : T' ⟶ T) (t : T ⟶ (diagonalizable X Λ).X) :
    pointsEquiv X Λ T' (a ≫ t) =
      (Units.map a.left.appTop.hom.toMonoidHom).comp (pointsEquiv X Λ T t) := by
  apply MonoidHom.ext
  intro m
  exact pointsEquiv_naturality a t m.toAdd

/-- Two homomorphisms out of `D_X(Λ)` agree when they agree on all character-valued points. -/
theorem hom_ext' {u v : diagonalizable X Λ ⟶ diagonalizable X Λ'}
    (h : ∀ (T : Over X) (t : T ⟶ (diagonalizable X Λ).X),
      pointsEquiv X Λ' T (t ≫ u.hom.hom) = pointsEquiv X Λ' T (t ≫ v.hom.hom)) :
    u = v :=
  hom_ext_points fun T t => (pointsEquiv X Λ' T).injective (h T t)

/-- `D_X(g)` acts on character-valued points by precomposition with `g`. -/
theorem pointsEquiv_diagonalizableMap (g : Λ' →+ Λ) (T : Over X)
    (t : T ⟶ (diagonalizable X Λ).X) :
    pointsEquiv X Λ' T (t ≫ (diagonalizableMap X g).hom.hom) =
      (pointsEquiv X Λ T t).comp (AddMonoidHom.toMultiplicative g) := by
  apply MonoidHom.ext
  intro m
  unfold pointsEquiv diagonalizableMap
  rw [MulEquiv.trans_apply, baseChangePointsEquiv_comp]
  exact Diagonalizable.pointsEquiv_restrictMap ZU.{u} g _ m.toAdd

@[simp]
theorem diagonalizableMap_id (X : Scheme.{u}) :
    diagonalizableMap X (AddMonoidHom.id Λ) = 𝟙 (diagonalizable X Λ) := by
  apply hom_ext'
  intro T t
  rw [pointsEquiv_diagonalizableMap, Grp.id_hom_hom, Category.comp_id]
  rfl

@[simp]
theorem diagonalizableMap_comp (X : Scheme.{u}) (g : Λ' →+ Λ) (h : Λ'' →+ Λ') :
    diagonalizableMap X g ≫ diagonalizableMap X h = diagonalizableMap X (g.comp h) := by
  unfold diagonalizableMap
  rw [← Functor.map_comp, Diagonalizable.restrictMap_comp]

/-- Changing the structure map to `Spec ℤ` along an equality does not change
character-valued points. -/
theorem characterPoints_eqToHom {c₁ c₂ : Y ⟶ Spec ZU.{u}} (hc : c₁ = c₂)
    (E : (GroupScheme.baseChange c₁).obj (Diagonalizable.groupScheme ZU.{u} Λ).toGrp =
      (GroupScheme.baseChange c₂).obj (Diagonalizable.groupScheme ZU.{u} Λ).toGrp)
    (T : Over Y)
    (s : T ⟶ ((GroupScheme.baseChange c₁).obj (Diagonalizable.groupScheme ZU.{u} Λ).toGrp).X) :
    Diagonalizable.characterPointsEquiv ZU.{u} Λ ((Over.map c₂).obj T)
        (baseChangePointsEquiv c₂ _ T (s ≫ (eqToHom E).hom.hom)) =
      Diagonalizable.characterPointsEquiv ZU.{u} Λ ((Over.map c₁).obj T)
        (baseChangePointsEquiv c₁ _ T s) := by
  subst hc
  rw [eqToHom_refl, Grp.id_hom_hom, Category.comp_id]

/-- The base-change comparison `D_X(Λ) ×_X Y ≅ D_Y(Λ)` preserves character-valued points. -/
theorem pointsEquiv_baseChangeIso_hom (b : Y ⟶ X) (T : Over Y)
    (t : T ⟶ ((GroupScheme.baseChange b).obj (diagonalizable X Λ)).X) :
    pointsEquiv Y Λ T (t ≫ (diagonalizableBaseChangeIso b Λ).hom.hom.hom) =
      pointsEquiv X Λ ((Over.map b).obj T)
        (baseChangePointsEquiv b (diagonalizable X Λ) T t) := by
  unfold pointsEquiv diagonalizableBaseChangeIso
  rw [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, Grp.comp_hom_hom, ← Category.assoc,
    MulEquiv.trans_apply, MulEquiv.trans_apply]
  refine (characterPoints_eqToHom (c₁ := b ≫ Gm.toSpecZ X) (c₂ := Gm.toSpecZ Y)
    (specULiftZIsTerminal.hom_ext _ _) _ T _).trans ?_
  rw [baseChangePointsEquiv_base_comp]
  apply MonoidHom.ext
  intro m
  have hn := Diagonalizable.characterPointsEquiv_naturality ZU.{u} Λ
    ((Over.mapComp b (Gm.toSpecZ X)).inv.app T)
    (baseChangePointsEquiv (b ≫ Gm.toSpecZ X) (Diagonalizable.groupScheme ZU.{u} Λ).toGrp T
      (t ≫ (baseChangeCompIso (Gm.toSpecZ X) b
        (Diagonalizable.groupScheme ZU.{u} Λ).toGrp).inv.hom.hom)) m.toAdd
  refine Eq.trans ?_ hn.symm
  rfl

/-- The inverse comparison, in the form used to transport homomorphisms. -/
theorem pointsEquiv_eq_baseChange (b : Y ⟶ X) (T : Over Y)
    (t : T ⟶ (diagonalizable Y Λ).X) :
    pointsEquiv Y Λ T t =
      pointsEquiv X Λ ((Over.map b).obj T) (baseChangePointsEquiv b (diagonalizable X Λ) T
        (t ≫ (diagonalizableBaseChangeIso b Λ).inv.hom.hom)) := by
  rw [← pointsEquiv_baseChangeIso_hom, Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id,
    Grp.id_hom_hom, Category.comp_id]

/-- The transport of `u` along `b` acts on character-valued points through `u`. -/
theorem pointsEquiv_transport (b : Y ⟶ X) (u : diagonalizable X Λ ⟶ diagonalizable X Λ')
    (T : Over Y) (t : T ⟶ (diagonalizable Y Λ).X) :
    pointsEquiv Y Λ' T (t ≫ ((diagonalizableBaseChangeIso b Λ).inv ≫
        (GroupScheme.baseChange b).map u ≫ (diagonalizableBaseChangeIso b Λ').hom).hom.hom) =
      pointsEquiv X Λ' ((Over.map b).obj T)
        (baseChangePointsEquiv b (diagonalizable X Λ) T
          (t ≫ (diagonalizableBaseChangeIso b Λ).inv.hom.hom) ≫ u.hom.hom) := by
  rw [Grp.comp_hom_hom, Grp.comp_hom_hom, ← Category.assoc, ← Category.assoc,
    pointsEquiv_baseChangeIso_hom, baseChangePointsEquiv_comp]

/-- `u` acts on the character-valued points over `T` by precomposition with `g`. -/
def ActsBy (u : diagonalizable X Λ ⟶ diagonalizable X Λ') (g : Λ' →+ Λ) (T : Over X) : Prop :=
  ∀ s : T ⟶ (diagonalizable X Λ).X,
    pointsEquiv X Λ' T (s ≫ u.hom.hom) =
      (pointsEquiv X Λ T s).comp (AddMonoidHom.toMultiplicative g)

theorem ActsBy.of_iso {u : diagonalizable X Λ ⟶ diagonalizable X Λ'} {g : Λ' →+ Λ}
    {T T' : Over X} (e : T' ≅ T) (h : ActsBy u g T) : ActsBy u g T' := by
  intro s
  have hs : s = e.hom ≫ (e.inv ≫ s) := by simp
  rw [hs, Category.assoc, pointsEquiv_comp e.hom, pointsEquiv_comp e.hom, h]
  rfl

/-- If `u` acts by `g` over every `X`-scheme coming from `Y`, then the base change of
`u` along `b` is `D_Y(g)`. -/
theorem baseChange_map_eq_of_actsBy (b : Y ⟶ X) (u : diagonalizable X Λ ⟶ diagonalizable X Λ')
    (g : Λ' →+ Λ) (h : ∀ T : Over Y, ActsBy u g ((Over.map b).obj T)) :
    (GroupScheme.baseChange b).map u =
      (diagonalizableBaseChangeIso b Λ).hom ≫ diagonalizableMap Y g ≫
        (diagonalizableBaseChangeIso b Λ').inv := by
  have key : (diagonalizableBaseChangeIso b Λ).inv ≫ (GroupScheme.baseChange b).map u ≫
      (diagonalizableBaseChangeIso b Λ').hom = diagonalizableMap Y g := by
    apply hom_ext'
    intro T t
    rw [pointsEquiv_transport, pointsEquiv_diagonalizableMap, h T, ← pointsEquiv_eq_baseChange]
  rw [← key]
  simp

/-- If `u` acts by `g` over a scheme from `Y` after transport along `b`, it acts by `g`
over the corresponding `X`-scheme. -/
theorem actsBy_of_transport (b : Y ⟶ X) (u : diagonalizable X Λ ⟶ diagonalizable X Λ')
    (g : Λ' →+ Λ) (T : Over Y)
    (h : ∀ t : T ⟶ (diagonalizable Y Λ).X,
      pointsEquiv Y Λ' T (t ≫ ((diagonalizableBaseChangeIso b Λ).inv ≫
        (GroupScheme.baseChange b).map u ≫ (diagonalizableBaseChangeIso b Λ').hom).hom.hom) =
      (pointsEquiv Y Λ T t).comp (AddMonoidHom.toMultiplicative g)) :
    ActsBy u g ((Over.map b).obj T) := by
  intro s
  let t : T ⟶ (diagonalizable Y Λ).X :=
    (baseChangePointsEquiv b (diagonalizable X Λ) T).symm s ≫
      (diagonalizableBaseChangeIso b Λ).hom.hom.hom
  have hs : baseChangePointsEquiv b (diagonalizable X Λ) T
      (t ≫ (diagonalizableBaseChangeIso b Λ).inv.hom.hom) = s := by
    simp only [t, Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom,
      Category.comp_id, MulEquiv.apply_symm_apply]
  have h1 := pointsEquiv_transport b u T t
  rw [hs] at h1
  rw [← h1, h t, pointsEquiv_eq_baseChange b T t, hs]

/-- `D_X(g)` is compatible with base change. -/
theorem baseChange_map_diagonalizableMap (b : Y ⟶ X) (g : Λ' →+ Λ) :
    (GroupScheme.baseChange b).map (diagonalizableMap X g) =
      (diagonalizableBaseChangeIso b Λ).hom ≫ diagonalizableMap Y g ≫
        (diagonalizableBaseChangeIso b Λ').inv :=
  baseChange_map_eq_of_actsBy b _ g fun _ s => pointsEquiv_diagonalizableMap g _ s

/-- Distinct character maps give distinct homomorphisms over a nonempty base. -/
theorem diagonalizableMap_injective [Nonempty X] :
    Function.Injective (diagonalizableMap X : (Λ' →+ Λ) → _) := by
  intro g g' h
  have : Nonempty (Over.mk (Gm.toSpecZ X)).left := ‹Nonempty X›
  exact Diagonalizable.restrictMap_baseChange_injective (Over.mk (Gm.toSpecZ X)) h

/-- On the affine base `Spec A`, character-valued points of `D_{Spec A}(Λ)` agree with those of
the group-algebra model. -/
theorem pointsEquiv_spec {A : CommRingCat.{u}} (T : Over (Spec A))
    (y : T ⟶ (diagonalizable (Spec A) Λ).X) :
    pointsEquiv (Spec A) Λ T y =
      Diagonalizable.characterPointsEquiv A Λ T
        (y ≫ (Diagonalizable.relativeModelIso A Λ).inv.hom.hom) :=
  (Diagonalizable.characterPointsEquiv_baseChangeIso_hom (Gm.toSpecZ (Spec A)) Λ T y).symm

/-- Affine core: a homomorphism which becomes `D(g)` after a base change `a` acts by `g` on the
points over every scheme coming from the source of `a`. -/
theorem characterPoints_of_baseChange_eq {A B : CommRingCat.{u}} (a : Spec B ⟶ Spec A)
    (f : (Diagonalizable.groupScheme A Λ).toGrp ⟶ (Diagonalizable.groupScheme A Λ').toGrp)
    (g : Λ' →+ Λ)
    (hf : (GroupScheme.baseChange a).map f =
      (GroupScheme.baseChange a).map (Diagonalizable.restrictMap A g))
    (T : Over (Spec B)) (y : (Over.map a).obj T ⟶ (Diagonalizable.groupScheme A Λ).X) :
    Diagonalizable.characterPointsEquiv A Λ' _ (y ≫ f.hom.hom) =
      (Diagonalizable.characterPointsEquiv A Λ _ y).comp
        (AddMonoidHom.toMultiplicative g) := by
  obtain ⟨y, rfl⟩ := (baseChangePointsEquiv a (Diagonalizable.groupScheme A Λ).toGrp T).surjective y
  rw [← baseChangePointsEquiv_comp, hf, baseChangePointsEquiv_comp]
  apply MonoidHom.ext
  intro m
  exact Diagonalizable.pointsEquiv_restrictMap A g _ m.toAdd

/-- The affine-local statement: given an open immersion `j : Spec A → X` and a point of
`Spec A`, there is an open neighborhood of its image on which `u` is `D(g)`. -/
theorem exists_opens_of_openImmersion [AddGroup.FG Λ'] {A : CommRingCat.{u}}
    (j : Spec A ⟶ X) [IsOpenImmersion j]
    (u : diagonalizable X Λ ⟶ diagonalizable X Λ') (z : Spec A) :
    ∃ U : X.Opens, j z ∈ U ∧ ∃ g : Λ' →+ Λ,
      (GroupScheme.baseChange U.ι).map u =
        (diagonalizableBaseChangeIso U.ι Λ).hom ≫ diagonalizableMap U g ≫
          (diagonalizableBaseChangeIso U.ι Λ').inv := by
  let uA : diagonalizable (Spec A) Λ ⟶ diagonalizable (Spec A) Λ' :=
    (diagonalizableBaseChangeIso j Λ).inv ≫ (GroupScheme.baseChange j).map u ≫
      (diagonalizableBaseChangeIso j Λ').hom
  let fA : (Diagonalizable.groupScheme A Λ).toGrp ⟶ (Diagonalizable.groupScheme A Λ').toGrp :=
    (Diagonalizable.relativeModelIso A Λ).hom ≫ uA ≫ (Diagonalizable.relativeModelIso A Λ').inv
  let p : PrimeSpectrum A := z
  obtain ⟨g, r, hr, hfA⟩ := Diagonalizable.exists_away_baseChange_map_eq_restrictMap fA p.asIdeal
  let a : Spec (CommRingCat.of (Localization.Away r)) ⟶ Spec A :=
    Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away r)))
  have : IsOpenImmersion a := IsOpenImmersion.of_isLocalization r
  refine ⟨(a ≫ j).opensRange, ?_, g, ?_⟩
  · obtain ⟨z', hz'⟩ : p ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away r))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
      exact hr
    refine Scheme.Hom.mem_opensRange.mpr ⟨z', ?_⟩
    rw [Scheme.Hom.comp_apply]
    congr 1
  · apply baseChange_map_eq_of_actsBy
    intro T
    let φ := (a ≫ j).isoOpensRange
    let T' : Over (Spec A) := (Over.map a).obj (Over.mk (T.hom ≫ φ.inv))
    let e : (Over.map (a ≫ j).opensRange.ι).obj T ≅ (Over.map j).obj T' :=
      Over.isoMk (Iso.refl _) (by
        simp [T', φ, Scheme.Hom.isoOpensRange_inv_comp])
    apply ActsBy.of_iso e
    apply actsBy_of_transport
    intro t
    rw [pointsEquiv_spec, pointsEquiv_spec]
    have hinv : (Diagonalizable.relativeModelIso A Λ).inv.hom.hom ≫
        (Diagonalizable.relativeModelIso A Λ).hom.hom.hom = 𝟙 _ := by
      rw [← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom]
    have ht : t ≫ uA.hom.hom ≫ (Diagonalizable.relativeModelIso A Λ').inv.hom.hom =
        (t ≫ (Diagonalizable.relativeModelIso A Λ).inv.hom.hom) ≫ fA.hom.hom := by
      simp only [fA, Grp.comp_hom_hom, Category.assoc, reassoc_of% hinv]
    change Diagonalizable.characterPointsEquiv A Λ' T'
        ((t ≫ uA.hom.hom) ≫ (Diagonalizable.relativeModelIso A Λ').inv.hom.hom) = _
    rw [Category.assoc, ht]
    exact characterPoints_of_baseChange_eq a fA g hfA _ _

/-- **Local rigidity.** Every homomorphism `D_X(Λ) → D_X(Λ')` is, Zariski-locally on `X`,
of the form `D(g)` for a homomorphism `g : Λ' →+ Λ`. -/
theorem exists_opens_baseChange_map_eq [AddGroup.FG Λ']
    (u : diagonalizable X Λ ⟶ diagonalizable X Λ') (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ g : Λ' →+ Λ,
      (GroupScheme.baseChange U.ι).map u =
        (diagonalizableBaseChangeIso U.ι Λ).hom ≫ diagonalizableMap U g ≫
          (diagonalizableBaseChangeIso U.ι Λ').inv := by
  obtain ⟨k, z, rfl⟩ := X.affineCover.exists_eq x
  exact exists_opens_of_openImmersion (X.affineCover.f k) u z

end Langlands.GroupScheme.RelativeMultiplicativeType
