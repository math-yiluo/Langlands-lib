import Langlands.Cohomology.AcyclicResolution.Comparison

/-!
# Left exact functors, homology and right derived functors

Let `Φ : D ⥤ E` be an additive functor between abelian categories that preserves finite
limits.

* `cyclesIso Φ S`: `Φ` of the cycles of a short complex `S` is the cycles of `S.map Φ`.
* `homologyHom Φ S : (S.map Φ).homology ⟶ Φ.obj S.homology` is the induced map on homology
  (`homologyπ_homologyHom`), natural in `S` (`homologyHom_naturality`). It is an isomorphism
  if `S.f = 0`, and if `Φ` also preserves homology (an exact functor).
* `homologyNatTrans Φ c i`: the same map for homological complexes, as a natural
  transformation `Φ.mapHomologicalComplex c ⋙ homologyFunctor E c i ⟶
  homologyFunctor D c i ⋙ Φ`. For cochain complexes indexed by `ℕ` it is an isomorphism in
  degree zero.
* `derivedHom Φ F I n` and `derivedNatTrans Φ F n : (F ⋙ Φ).rightDerived n ⟶
  F.rightDerived n ⋙ Φ`: for an additive `F : C ⥤ D`, the map induced by `homologyNatTrans`
  on `F` of an injective resolution `I`. It does not depend on `I` (`derivedHom_eq`). It is an
  isomorphism in degree zero, and if `Φ` preserves homology.
* `comparison_comp_derivedHom`, `comparisonNatTrans_comp_derivedNatTrans`: the comparison
  maps of `AcyclicResolution` for `F ⋙ Φ` and for `F` are compatible with these maps.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace Langlands.Cohomology.LeftExactHomology

universe v u v' u' v'' u''

variable {D : Type u} [Category.{v} D] [Abelian D] {E : Type u'} [Category.{v'} E] [Abelian E]
  (Φ : D ⥤ E) [Φ.Additive] [PreservesFiniteLimits Φ]

section ShortComplex

variable (S : ShortComplex D)

/-- `Φ` of the cycles of `S` maps to the cycles of `S.map Φ`, through `Φ` of the inclusion of
the cycles. -/
def toCycles : Φ.obj S.cycles ⟶ (S.map Φ).cycles :=
  (S.map Φ).liftCycles (Φ.map S.iCycles)
    ((Φ.map_comp _ _).symm.trans ((congrArg Φ.map S.iCycles_g).trans (Φ.map_zero _ _)))

omit [PreservesFiniteLimits Φ] in
/-- The map `toCycles Φ S` followed by the inclusion of the cycles of `S.map Φ` is `Φ` of the
inclusion of the cycles of `S`. -/
@[reassoc (attr := simp)]
lemma toCycles_iCycles : toCycles Φ S ≫ (S.map Φ).iCycles = Φ.map S.iCycles :=
  (S.map Φ).liftCycles_i _ _

/-- Since `Φ` preserves kernels, `Φ` of the cycles of `S` is the cycles of `S.map Φ`. -/
def cyclesIso : Φ.obj S.cycles ≅ (S.map Φ).cycles :=
  IsLimit.conePointUniqueUpToIso (KernelFork.mapIsLimit _ S.cyclesIsKernel Φ)
    (S.map Φ).cyclesIsKernel

/-- The isomorphism `cyclesIso Φ S` is the map `toCycles Φ S`. -/
lemma cyclesIso_hom : (cyclesIso Φ S).hom = toCycles Φ S := by
  rw [← cancel_mono (S.map Φ).iCycles, toCycles_iCycles]
  exact IsLimit.conePointUniqueUpToIso_hom_comp (KernelFork.mapIsLimit _ S.cyclesIsKernel Φ)
    (S.map Φ).cyclesIsKernel WalkingParallelPair.zero

instance isIso_toCycles : IsIso (toCycles Φ S) := by
  rw [← cyclesIso_hom]
  infer_instance

omit [PreservesFiniteLimits Φ] in
/-- `Φ` of the map from `S.X₁` to the cycles, followed by `toCycles Φ S`, is the map from the
first object of `S.map Φ` to its cycles. -/
@[reassoc (attr := simp)]
lemma map_toCycles_comp_toCycles : Φ.map S.toCycles ≫ toCycles Φ S = (S.map Φ).toCycles := by
  rw [← cancel_mono (S.map Φ).iCycles, Category.assoc, toCycles_iCycles, ← Φ.map_comp,
    S.toCycles_i, ShortComplex.toCycles_i]
  rfl

/-- The map from the homology of `S.map Φ` to `Φ` of the homology of `S`: the inverse of
`toCycles Φ S` followed by `Φ` of the projection from the cycles to the homology, which
vanishes on the boundaries. -/
def homologyHom : (S.map Φ).homology ⟶ Φ.obj S.homology :=
  (S.map Φ).descHomology (inv (toCycles Φ S) ≫ Φ.map S.homologyπ) (by
    rw [← map_toCycles_comp_toCycles, Category.assoc, IsIso.hom_inv_id_assoc, ← Φ.map_comp,
      S.toCycles_comp_homologyπ, Φ.map_zero])

/-- The projection to the homology of `S.map Φ` followed by `homologyHom Φ S` is the inverse
of `toCycles Φ S` followed by `Φ` of the projection to the homology of `S`. -/
@[reassoc (attr := simp)]
lemma homologyπ_homologyHom :
    (S.map Φ).homologyπ ≫ homologyHom Φ S = inv (toCycles Φ S) ≫ Φ.map S.homologyπ :=
  (S.map Φ).π_descHomology _ _

/-- `toCycles Φ S` followed by the projection to the homology of `S.map Φ` and
`homologyHom Φ S` is `Φ` of the projection to the homology of `S`. -/
@[reassoc (attr := simp)]
lemma toCycles_homologyπ_homologyHom :
    toCycles Φ S ≫ (S.map Φ).homologyπ ≫ homologyHom Φ S = Φ.map S.homologyπ := by
  rw [homologyπ_homologyHom, IsIso.hom_inv_id_assoc]

omit [PreservesFiniteLimits Φ] in
variable {S} in
/-- The maps `toCycles` are natural. -/
@[reassoc]
lemma toCycles_naturality {S' : ShortComplex D} (φ : S ⟶ S') :
    toCycles Φ S ≫ ShortComplex.cyclesMap (Φ.mapShortComplex.map φ) =
      Φ.map (ShortComplex.cyclesMap φ) ≫ toCycles Φ S' := by
  have h : ShortComplex.cyclesMap (Φ.mapShortComplex.map φ) ≫ (S'.map Φ).iCycles =
      (S.map Φ).iCycles ≫ Φ.map φ.τ₂ :=
    ShortComplex.cyclesMap_i _
  rw [← cancel_mono (S'.map Φ).iCycles, Category.assoc, Category.assoc, h,
    toCycles_iCycles_assoc, toCycles_iCycles, ← Φ.map_comp, ← Φ.map_comp,
    ShortComplex.cyclesMap_i]

variable {S} in
/-- The maps `homologyHom` are natural. -/
@[reassoc]
lemma homologyHom_naturality {S' : ShortComplex D} (φ : S ⟶ S') :
    ShortComplex.homologyMap (Φ.mapShortComplex.map φ) ≫ homologyHom Φ S' =
      homologyHom Φ S ≫ Φ.map (ShortComplex.homologyMap φ) := by
  have h : (S.map Φ).homologyπ ≫ ShortComplex.homologyMap (Φ.mapShortComplex.map φ) ≫
      homologyHom Φ S' = ShortComplex.cyclesMap (Φ.mapShortComplex.map φ) ≫
        (S'.map Φ).homologyπ ≫ homologyHom Φ S' :=
    ShortComplex.homologyπ_naturality_assoc _ _
  rw [← cancel_epi (toCycles Φ S ≫ (S.map Φ).homologyπ), Category.assoc, h,
    toCycles_naturality_assoc, toCycles_homologyπ_homologyHom, Category.assoc,
    toCycles_homologyπ_homologyHom_assoc, ← Φ.map_comp, ← Φ.map_comp,
    ShortComplex.homologyπ_naturality]

/-- If the first map of `S` vanishes, `homologyHom Φ S` is an isomorphism. -/
lemma isIso_homologyHom_of_f_eq_zero (hf : S.f = 0) : IsIso (homologyHom Φ S) := by
  have := S.isIso_homologyπ hf
  have : IsIso (S.map Φ).homologyπ :=
    (S.map Φ).isIso_homologyπ ((congrArg Φ.map hf).trans (Φ.map_zero _ _))
  have h : homologyHom Φ S = inv (S.map Φ).homologyπ ≫ inv (toCycles Φ S) ≫ Φ.map S.homologyπ := by
    rw [← homologyπ_homologyHom, IsIso.inv_hom_id_assoc]
  rw [h]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- If `Φ` also preserves homology, `homologyHom Φ S` is an isomorphism. -/
instance isIso_homologyHom [Φ.PreservesHomology] : IsIso (homologyHom Φ S) := by
  let h := S.leftHomologyData
  have e : homologyHom Φ S =
      ((h.map Φ).homologyIso ≪≫ Φ.mapIso h.homologyIso.symm).hom := by
    rw [← cancel_epi (toCycles Φ S ≫ (S.map Φ).homologyπ), Category.assoc,
      toCycles_homologyπ_homologyHom, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      Category.assoc, ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc]
    have hc : toCycles Φ S ≫ (h.map Φ).cyclesIso.hom = Φ.map h.cyclesIso.hom := by
      rw [← cancel_mono (h.map Φ).i, Category.assoc,
        ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i, toCycles_iCycles,
        ShortComplex.LeftHomologyData.map_i, ← Φ.map_comp,
        ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i]
    rw [reassoc_of% hc, ShortComplex.LeftHomologyData.map_π, ← Φ.map_comp, ← Φ.map_comp,
      ShortComplex.LeftHomologyData.π_comp_homologyIso_inv, ← Category.assoc, Iso.hom_inv_id,
      Category.id_comp]
  rw [e]
  infer_instance

end ShortComplex

section HomologicalComplex

variable {ι : Type*} (c : ComplexShape ι) (i : ι)

/-- The maps `homologyHom` for homological complexes, as a natural transformation from the
homology of `Φ` applied to a complex to `Φ` of its homology. -/
def homologyNatTrans :
    Φ.mapHomologicalComplex c ⋙ HomologicalComplex.homologyFunctor E c i ⟶
      HomologicalComplex.homologyFunctor D c i ⋙ Φ where
  app K := homologyHom Φ (K.sc i)
  naturality _ _ f := homologyHom_naturality Φ ((HomologicalComplex.shortComplexFunctor D c i).map f)

/-- The component of `homologyNatTrans Φ c i` at `K` is `homologyHom Φ (K.sc i)`. -/
lemma homologyNatTrans_app (K : HomologicalComplex D c) :
    (homologyNatTrans Φ c i).app K = homologyHom Φ (K.sc i) :=
  rfl

/-- If `Φ` also preserves homology, `homologyNatTrans Φ c i` is an isomorphism. -/
instance isIso_homologyNatTrans [Φ.PreservesHomology] : IsIso (homologyNatTrans Φ c i) :=
  have : ∀ K : HomologicalComplex D c, IsIso ((homologyNatTrans Φ c i).app K) :=
    fun K => isIso_homologyHom Φ (K.sc i)
  NatIso.isIso_of_isIso_app _

/-- For cochain complexes indexed by `ℕ`, `homologyNatTrans` is an isomorphism in degree
zero, where homology is the cycles. -/
instance isIso_homologyNatTrans_zero :
    IsIso (homologyNatTrans Φ (ComplexShape.up ℕ) 0) :=
  have : ∀ K : CochainComplex D ℕ, IsIso ((homologyNatTrans Φ (ComplexShape.up ℕ) 0).app K) :=
    fun K => isIso_homologyHom_of_f_eq_zero Φ (K.sc 0) (K.shape _ _ (by simp))
  NatIso.isIso_of_isIso_app _

end HomologicalComplex

section Derived

variable {C : Type u''} [Category.{v''} C] [Abelian C] [HasInjectiveResolutions C]
  (F : C ⥤ D) [F.Additive]

/-- The map `Rⁿ(F ⋙ Φ) A ⟶ Φ (Rⁿ F A)` computed with an injective resolution `I` of `A`:
`homologyNatTrans` on `F` applied to `I`, between Mathlib's identifications of both derived
functors with the homology of `I`. -/
def derivedHom {A : C} (I : InjectiveResolution A) (n : ℕ) :
    ((F ⋙ Φ).rightDerived n).obj A ⟶ Φ.obj ((F.rightDerived n).obj A) :=
  (I.isoRightDerivedObj (F ⋙ Φ) n).hom ≫
    (homologyNatTrans Φ (ComplexShape.up ℕ) n).app ((F.mapHomologicalComplex _).obj I.cocomplex) ≫
      Φ.map (I.isoRightDerivedObj F n).inv

/-- The maps `derivedHom` are natural in the resolved object, for every cochain map of
injective resolutions over a given morphism. -/
theorem derivedHom_naturality {A B : C} (f : A ⟶ B) (I : InjectiveResolution A)
    (J : InjectiveResolution B) (ψ : I.cocomplex ⟶ J.cocomplex)
    (comm : I.ι.f 0 ≫ ψ.f 0 = f ≫ J.ι.f 0) (n : ℕ) :
    ((F ⋙ Φ).rightDerived n).map f ≫ derivedHom Φ F J n =
      derivedHom Φ F I n ≫ Φ.map ((F.rightDerived n).map f) := by
  have h₁ := InjectiveResolution.isoRightDerivedObj_hom_naturality f I J ψ comm (F ⋙ Φ) n
  have h₂ := (homologyNatTrans Φ (ComplexShape.up ℕ) n).naturality
    ((F.mapHomologicalComplex _).map ψ)
  have h₃ := InjectiveResolution.isoRightDerivedObj_inv_naturality f I J ψ comm F n
  rw [derivedHom, derivedHom, ← Category.assoc, h₁, Category.assoc, Category.assoc,
    Category.assoc, ← Φ.map_comp, h₃, Φ.map_comp]
  congr 1
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ Φ.map (J.isoRightDerivedObj F n).inv) h₂).trans (Category.assoc _ _ _))

/-- The map `derivedHom Φ F I n` does not depend on the injective resolution `I`. -/
theorem derivedHom_eq {A : C} (I J : InjectiveResolution A) (n : ℕ) :
    derivedHom Φ F I n = derivedHom Φ F J n := by
  have h := derivedHom_naturality Φ F (𝟙 A) I J (InjectiveResolution.desc (𝟙 A) J I)
    (InjectiveResolution.desc_commutes_zero _ _ _) n
  rwa [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id, eq_comm] at h

/-- The natural transformation `Rⁿ(F ⋙ Φ) ⟶ Rⁿ F ⋙ Φ` whose components are the maps
`derivedHom` for Mathlib's chosen injective resolutions. -/
def derivedNatTrans (n : ℕ) : (F ⋙ Φ).rightDerived n ⟶ F.rightDerived n ⋙ Φ where
  app A := derivedHom Φ F (injectiveResolution A) n
  naturality _ _ f := derivedHom_naturality Φ F f _ _ _
    (InjectiveResolution.desc_commutes_zero _ _ _) n

/-- Each component of `derivedNatTrans Φ F n` is `derivedHom` for every injective
resolution. -/
theorem derivedNatTrans_app {A : C} (I : InjectiveResolution A) (n : ℕ) :
    (derivedNatTrans Φ F n).app A = derivedHom Φ F I n :=
  derivedHom_eq Φ F _ I n

/-- In degree zero, `derivedNatTrans Φ F` is an isomorphism. -/
instance isIso_derivedNatTrans_zero : IsIso (derivedNatTrans Φ F 0) :=
  have : ∀ A, IsIso ((derivedNatTrans Φ F 0).app A) := fun A => by
    change IsIso (derivedHom Φ F (injectiveResolution A) 0)
    rw [derivedHom]
    infer_instance
  NatIso.isIso_of_isIso_app _

/-- If `Φ` also preserves homology, `derivedNatTrans Φ F n` is an isomorphism. -/
instance isIso_derivedNatTrans [Φ.PreservesHomology] (n : ℕ) :
    IsIso (derivedNatTrans Φ F n) :=
  have : ∀ A, IsIso ((derivedNatTrans Φ F n).app A) := fun A => by
    change IsIso (derivedHom Φ F (injectiveResolution A) n)
    rw [derivedHom]
    infer_instance
  NatIso.isIso_of_isIso_app _

/-- The comparison map of `AcyclicResolution` for `F ⋙ Φ`, followed by `derivedHom`, is
`homologyNatTrans` followed by `Φ` of the comparison map for `F`. -/
theorem comparison_comp_derivedHom {A : C} {K : CochainComplex C ℕ}
    (I : InjectiveResolution A) (φ : K ⟶ I.cocomplex) (n : ℕ) :
    AcyclicResolution.comparison (F ⋙ Φ) I φ n ≫ derivedHom Φ F I n =
      (homologyNatTrans Φ (ComplexShape.up ℕ) n).app ((F.mapHomologicalComplex _).obj K) ≫
        Φ.map (AcyclicResolution.comparison F I φ n) := by
  have h := (homologyNatTrans Φ (ComplexShape.up ℕ) n).naturality
    ((F.mapHomologicalComplex _).map φ)
  rw [AcyclicResolution.comparison, AcyclicResolution.comparison, derivedHom, Category.assoc,
    Iso.inv_hom_id_assoc, Φ.map_comp]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ Φ.map (I.isoRightDerivedObj F n).inv) h).trans (Category.assoc _ _ _))

variable (𝒦 : C ⥤ CochainComplex C ℕ) (e : CochainComplex.single₀ C ⟶ 𝒦)
  (he : ∀ A, QuasiIso (e.app A))

/-- The comparison transformation of a functorial right resolution for `F ⋙ Φ`, followed by
`derivedNatTrans`, is `homologyNatTrans` followed by `Φ` of the comparison transformation
for `F`. -/
theorem comparisonNatTrans_comp_derivedNatTrans (n : ℕ) :
    AcyclicResolution.comparisonNatTrans (F ⋙ Φ) 𝒦 e he n ≫ derivedNatTrans Φ F n =
      Functor.whiskerLeft (𝒦 ⋙ F.mapHomologicalComplex _)
          (homologyNatTrans Φ (ComplexShape.up ℕ) n) ≫
        Functor.whiskerRight (AcyclicResolution.comparisonNatTrans F 𝒦 e he n) Φ := by
  refine NatTrans.ext (funext fun A => ?_)
  have := he A
  have hφ := AcyclicResolution.comp_lift_id (e.app A) (injectiveResolution A)
  change (AcyclicResolution.comparisonNatTrans (F ⋙ Φ) 𝒦 e he n).app A ≫
      (derivedNatTrans Φ F n).app A = _ ≫
        Φ.map ((AcyclicResolution.comparisonNatTrans F 𝒦 e he n).app A)
  rw [AcyclicResolution.comparisonNatTrans_app _ _ _ he A _ _ hφ,
    AcyclicResolution.comparisonNatTrans_app _ _ _ he A _ _ hφ,
    derivedNatTrans_app Φ F (injectiveResolution A)]
  exact comparison_comp_derivedHom Φ F _ _ n

end Derived

end Langlands.Cohomology.LeftExactHomology
