import Langlands.AlgebraicGeometry.Modules.BiCech.ProductSections
import Langlands.Cohomology.ModuleComplex.TensorSignsUpNat
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Global sections of the bi-Čech complex are the tensor total complex

In the setting of `BiCech.ProductSections`, assume that all finite intersections of the covers
`𝒰` and `𝒱` are affine and carry frames of `L` and `M`. Then the complex of `R`-module global
sections of the bi-Čech complex of `F = p₁^* L ⊗ p₂^* M` is isomorphic to the total complex
`HomologicalComplex.mapBifunctor C(𝒰, L) C(𝒱, M) (curriedTensor _) (up ℕ)` of the tensor
product of the Čech cochain complexes of the factors.

In degree `n` the map from the total complex sends the summand `C^p(𝒰, L) ⊗ C^q(𝒱, M)`,
`p + q = n`, by the bijective cup map `cupFam p q` onto the global sections concentrated in
bidegree `(p, q)` (`insT`); its inverse sums, over the bidegrees, the inverse cup maps of the
components. The differentials agree by `D_insT` and the compatibility of the cup map with the
Čech differentials of the factors; the signs of the total complex come from
`Langlands.Cohomology.ModuleComplex.tensorSignsUpNat`.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
  MonoidalCategory
open scoped TensorProduct

noncomputable section

namespace Langlands.AlgebraicGeometry.Modules.BiCech

open CechResolution Scheme.Modules OModulePresheaf

variable {R : CommRingCat.{u}} {X Y P : Scheme.{u}} {πX : X ⟶ Spec R} {πY : Y ⟶ Spec R}
  {p₁ : P ⟶ X} {p₂ : P ⟶ Y} {πP : P ⟶ Spec R} (hπ : p₁ ≫ πX = πP)
  (hP : IsPullback p₁ p₂ πX πY) (𝒰 : X.OrderedAffineCover) (𝒱 : Y.OrderedAffineCover)
  (L : X.Modules) (M : Y.Modules)

section General

variable {P : Scheme.{u}} {𝒲 : BiCover P} {F : P.Modules}

lemma insT_add {n p q : ℕ} (h : p + q = n)
    (c c' : ∀ (s : 𝒲.𝒰.Idx p) (t : 𝒲.𝒱.Idx q), Γ(F, biOpen 𝒲 s t)) :
    insT h (c + c') = insT h c + insT h c' := by
  rw [compF_eq_iff]
  intro p' q' h' s' t'
  rw [compF_add]
  by_cases e : (p', q') = (p, q)
  · obtain ⟨hp, hq⟩ := Prod.mk.inj e
    subst hp hq
    rw [compF_insT_self, compF_insT_self, compF_insT_self]
    rfl
  · rw [compF_insT_ne _ _ e, compF_insT_ne _ _ e, compF_insT_ne _ _ e, add_zero]

lemma algebraMap_biOpen (π : P ⟶ Spec R) {p q : ℕ} (s : 𝒲.𝒰.Idx p) (t : 𝒲.𝒱.Idx q) (r : R) :
    P.presheaf.map (homOfLE (biOpen_le_bo s t)).op
        (((biOpen 𝒲 s t).ι.app ⊤ ≫ ((biOpen 𝒲 s t).ι.appIso ((biOpen 𝒲 s t).ι ⁻¹ᵁ ⊤)).inv)
          ((DerivedSections.structureRingHom π).hom r)) =
      (Scheme.TwoAffineOpenCover.algebraOfHom π (biOpen 𝒲 s t)).algebraMap r := by
  rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom]
  exact congrArg (fun φ => (ConcreteCategory.hom φ) r)
    (structureRingHom_comp_biOpen π (biOpen 𝒲 s t) (biOpen_le_bo s t))

/-- A global section of the `R`-module of global sections, as a section of the term. -/
def asΓ {π : P ⟶ Spec R} {n : ℕ}
    (z : (DerivedSections.relativeGlobalSections π).obj (term 𝒲 F n)) : Γ(term 𝒲 F n, ⊤) :=
  z

lemma asΓ_sum {π : P ⟶ Spec R} {n : ℕ} {ι : Type*} (S : Finset ι)
    (z : ι → (DerivedSections.relativeGlobalSections π).obj (term 𝒲 F n)) :
    asΓ (∑ i ∈ S, z i) = ∑ i ∈ S, asΓ (z i) :=
  map_sum (AddMonoidHom.mk' (asΓ (π := π) (𝒲 := 𝒲) (F := F) (n := n)) fun _ _ => rfl) z S

lemma asΓ_add {π : P ⟶ Spec R} {n : ℕ}
    (z z' : (DerivedSections.relativeGlobalSections π).obj (term 𝒲 F n)) :
    asΓ (z + z') = asΓ z + asΓ z' :=
  rfl

lemma asΓ_zsmul {π : P ⟶ Spec R} {n : ℕ} (k : ℤ)
    (z : (DerivedSections.relativeGlobalSections π).obj (term 𝒲 F n)) :
    asΓ (k • z) = k • asΓ z :=
  map_zsmul (AddMonoidHom.mk' (asΓ (π := π) (𝒲 := 𝒲) (F := F) (n := n)) fun _ _ => rfl) k z

/-- A family of `R`-module sections, as a family of sections. -/
def famΓ {π : P ⟶ Spec R} {p q : ℕ}
    (c : ∀ (s : 𝒲.𝒰.Idx p) (t : 𝒲.𝒱.Idx q), (ofModules π F).obj (biOpen 𝒲 s t)) :
    ∀ (s : 𝒲.𝒰.Idx p) (t : 𝒲.𝒱.Idx q), Γ(F, biOpen 𝒲 s t) :=
  c

lemma famΓ_zero {π : P ⟶ Spec R} {p q : ℕ} :
    famΓ (π := π) (𝒲 := 𝒲) (F := F) (p := p) (q := q) 0 = fun _ _ => 0 :=
  rfl

variable (𝒲 F)

/-- The insertion of a bidegree-`(p, q)` family as an `R`-linear map. -/
def insLin (π : P ⟶ Spec R) {n p q : ℕ} (h : p + q = n) :
    (∀ (s : 𝒲.𝒰.Idx p) (t : 𝒲.𝒱.Idx q), (ofModules π F).obj (biOpen 𝒲 s t)) →ₗ[R]
      (DerivedSections.relativeGlobalSections π).obj (term 𝒲 F n) where
  toFun c := insT h c
  map_add' c c' := insT_add h c c'
  map_smul' r c := by
    change insT h (r • c) = (DerivedSections.structureRingHom π).hom r • insT h c
    rw [compF_eq_iff]
    intro p' q' h' s' t'
    rw [compF_smul, algebraMap_biOpen]
    by_cases e : (p', q') = (p, q)
    · obtain ⟨hp, hq⟩ := Prod.mk.inj e
      subst hp hq
      rw [compF_insT_self h h' (r • c) s' t', compF_insT_self h h' c s' t']
      rfl
    · rw [compF_insT_ne h h' e (r • c) s' t', compF_insT_ne h h' e c s' t', smul_zero]

/-- The bidegree-`(p, q)` components as an `R`-linear map. -/
def compLin (π : P ⟶ Spec R) {n : ℕ} (p q : ℕ) (h : p + q = n) :
    (DerivedSections.relativeGlobalSections π).obj (term 𝒲 F n) →ₗ[R]
      ∀ (s : 𝒲.𝒰.Idx p) (t : 𝒲.𝒱.Idx q), (ofModules π F).obj (biOpen 𝒲 s t) where
  toFun z s t := compF (show Γ(term 𝒲 F n, ⊤) from z) p q h s t
  map_add' z z' := funext fun s => funext fun t => compF_add (𝒲 := 𝒲) (F := F) z z' p q h s t
  map_smul' r z := funext fun s => funext fun t => by
    change compF ((DerivedSections.structureRingHom π).hom r • (show Γ(term 𝒲 F n, ⊤) from z))
      p q h s t = _
    rw [compF_smul, algebraMap_biOpen]
    rfl

end General

section Product

variable (hU : ∀ (p : ℕ) (s : 𝒰.Idx p), IsAffineOpen (𝒰.inter s))
  (hV : ∀ (q : ℕ) (t : 𝒱.Idx q), IsAffineOpen (𝒱.inter t))
  (hL : ∀ (p : ℕ) (s : 𝒰.Idx p), ∃ e : Γ(L, 𝒰.inter s), IsFrameOn e (𝒰.inter s))
  (hM : ∀ (q : ℕ) (t : 𝒱.Idx q), ∃ e : Γ(M, 𝒱.inter t), IsFrameOn e (𝒱.inter t))

/-- The cup map on families, on the tensor product in `ModuleCat`. -/
def cupFamT (p q : ℕ) :
    ((curriedTensor (ModuleCat.{u} R)).obj ((cechCochainComplex πX 𝒰 L).X p)).obj
      ((cechCochainComplex πY 𝒱 M).X q) →ₗ[R]
      ∀ (s : 𝒰.Idx p) (t : 𝒱.Idx q),
        (ofModules πP (extTensor p₁ p₂ L M)).obj (biOpen (prodBiCover p₁ p₂ 𝒰 𝒱) s t) :=
  cupFam hπ hP 𝒰 𝒱 L M p q

/-- The cup map on families as a linear equivalence. -/
def cupFamEquiv (p q : ℕ) :
    ((curriedTensor (ModuleCat.{u} R)).obj ((cechCochainComplex πX 𝒰 L).X p)).obj
      ((cechCochainComplex πY 𝒱 M).X q) ≃ₗ[R]
      ∀ (s : 𝒰.Idx p) (t : 𝒱.Idx q),
        (ofModules πP (extTensor p₁ p₂ L M)).obj (biOpen (prodBiCover p₁ p₂ 𝒰 𝒱) s t) :=
  LinearEquiv.ofBijective (cupFamT hπ hP 𝒰 𝒱 L M p q)
    (cupFam_bijective hπ hP 𝒰 𝒱 L M p q (hU p) (hV q) (hL p) (hM q))

variable (πX πY) in
/-- The tensor total complex of the Čech cochain complexes of the factors. -/
abbrev totCech : CochainComplex (ModuleCat.{u} R) ℕ :=
  HomologicalComplex.mapBifunctor (cechCochainComplex πX 𝒰 L) (cechCochainComplex πY 𝒱 M)
    (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℕ)

variable (πP p₁ p₂) in
/-- The complex of `R`-module global sections of the bi-Čech complex. -/
abbrev sectionsBicech : CochainComplex (ModuleCat.{u} R) ℕ :=
  ((DerivedSections.relativeGlobalSections πP).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (bicechComplex (prodBiCover p₁ p₂ 𝒰 𝒱) (extTensor p₁ p₂ L M))

/-- A global section of the bi-Čech complex, as a section of the term. -/
def toΓ {n : ℕ} (z : (sectionsBicech p₁ p₂ πP 𝒰 𝒱 L M).X n) :
    Γ(term (prodBiCover p₁ p₂ 𝒰 𝒱) (extTensor p₁ p₂ L M) n, ⊤) :=
  z

/-- A section of the term, as a global section of the bi-Čech complex. -/
def ofΓ {n : ℕ} (z : Γ(term (prodBiCover p₁ p₂ 𝒰 𝒱) (extTensor p₁ p₂ L M) n, ⊤)) :
    (sectionsBicech p₁ p₂ πP 𝒰 𝒱 L M).X n :=
  z

lemma toΓ_sum {n : ℕ} {ι : Type*} (S : Finset ι)
    (z : ι → (sectionsBicech p₁ p₂ πP 𝒰 𝒱 L M).X n) :
    toΓ 𝒰 𝒱 L M (∑ i ∈ S, z i) = ∑ i ∈ S, toΓ 𝒰 𝒱 L M (z i) :=
  map_sum (AddMonoidHom.mk' (toΓ (πP := πP) 𝒰 𝒱 L M (n := n)) fun _ _ => rfl) z S

lemma toΓ_add {n : ℕ} (z z' : (sectionsBicech p₁ p₂ πP 𝒰 𝒱 L M).X n) :
    toΓ 𝒰 𝒱 L M (z + z') = toΓ 𝒰 𝒱 L M z + toΓ 𝒰 𝒱 L M z' :=
  rfl

lemma toΓ_zsmul {n : ℕ} (k : ℤ) (z : (sectionsBicech p₁ p₂ πP 𝒰 𝒱 L M).X n) :
    toΓ 𝒰 𝒱 L M (k • z) = k • toΓ 𝒰 𝒱 L M z :=
  map_zsmul (AddMonoidHom.mk' (toΓ (πP := πP) 𝒰 𝒱 L M (n := n)) fun _ _ => rfl) k z

/-- `insLin`, with values in the global sections of the bi-Čech complex. -/
def insLin' {n p q : ℕ} (h : p + q = n) :
    (∀ (s : 𝒰.Idx p) (t : 𝒱.Idx q),
      (ofModules πP (extTensor p₁ p₂ L M)).obj (biOpen (prodBiCover p₁ p₂ 𝒰 𝒱) s t)) →ₗ[R]
      (sectionsBicech p₁ p₂ πP 𝒰 𝒱 L M).X n :=
  insLin (prodBiCover p₁ p₂ 𝒰 𝒱) (extTensor p₁ p₂ L M) πP h

/-- `compLin`, on the global sections of the bi-Čech complex. -/
def compLin' {n : ℕ} (p q : ℕ) (h : p + q = n) :
    (sectionsBicech p₁ p₂ πP 𝒰 𝒱 L M).X n →ₗ[R]
      ∀ (s : 𝒰.Idx p) (t : 𝒱.Idx q),
        (ofModules πP (extTensor p₁ p₂ L M)).obj (biOpen (prodBiCover p₁ p₂ 𝒰 𝒱) s t) :=
  compLin (prodBiCover p₁ p₂ 𝒰 𝒱) (extTensor p₁ p₂ L M) πP p q h

/-- The degree-`n` map from the tensor total complex to the global sections of the bi-Čech
complex. -/
def sectionsHom (n : ℕ) : (totCech πX πY 𝒰 𝒱 L M).X n ⟶ (sectionsBicech p₁ p₂ πP 𝒰 𝒱 L M).X n :=
  HomologicalComplex.mapBifunctorDesc fun p q h =>
    ModuleCat.ofHom (Y := (sectionsBicech p₁ p₂ πP 𝒰 𝒱 L M).X n)
      ((insLin' 𝒰 𝒱 L M h) ∘ₗ cupFamT hπ hP 𝒰 𝒱 L M p q)

lemma ι_sectionsHom (n p q : ℕ) (h : p + q = n) :
    HomologicalComplex.ιMapBifunctor (cechCochainComplex πX 𝒰 L)
        (cechCochainComplex πY 𝒱 M) (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℕ)
        p q n h ≫ sectionsHom hπ hP 𝒰 𝒱 L M n =
      ModuleCat.ofHom (Y := (sectionsBicech p₁ p₂ πP 𝒰 𝒱 L M).X n)
        ((insLin' 𝒰 𝒱 L M h) ∘ₗ cupFamT hπ hP 𝒰 𝒱 L M p q) :=
  HomologicalComplex.ι_mapBifunctorDesc _ p q h

lemma ι_sectionsHom_apply (n p q : ℕ) (h : p + q = n)
    (x : ((curriedTensor (ModuleCat.{u} R)).obj ((cechCochainComplex πX 𝒰 L).X p)).obj
      ((cechCochainComplex πY 𝒱 M).X q)) :
    toΓ 𝒰 𝒱 L M ((sectionsHom hπ hP 𝒰 𝒱 L M n).hom
        ((HomologicalComplex.ιMapBifunctor (cechCochainComplex πX 𝒰 L)
          (cechCochainComplex πY 𝒱 M) (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℕ)
          p q n h).hom x)) =
      insT (𝒲 := prodBiCover p₁ p₂ 𝒰 𝒱) (F := extTensor p₁ p₂ L M) h
        (famΓ (cupFamT hπ hP 𝒰 𝒱 L M p q x)) :=
  congrArg (fun φ => ModuleCat.Hom.hom φ x) (ι_sectionsHom hπ hP 𝒰 𝒱 L M n p q h)

include hU hV hL hM in
/-- The `(p, q)`-summand of the inverse map. -/
def invComponent (n : ℕ) (pq : Finset.HasAntidiagonal.antidiagonal n) :
    (sectionsBicech p₁ p₂ πP 𝒰 𝒱 L M).X n →ₗ[R] (totCech πX πY 𝒰 𝒱 L M).X n :=
  (HomologicalComplex.ιMapBifunctor (cechCochainComplex πX 𝒰 L) (cechCochainComplex πY 𝒱 M)
      (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℕ) pq.1.1 pq.1.2 n
      (Finset.HasAntidiagonal.mem_antidiagonal.1 pq.2)).hom ∘ₗ
    ((cupFamEquiv hπ hP 𝒰 𝒱 L M hU hV hL hM pq.1.1 pq.1.2).symm.toLinearMap ∘ₗ
      compLin' 𝒰 𝒱 L M pq.1.1 pq.1.2 (Finset.HasAntidiagonal.mem_antidiagonal.1 pq.2))

lemma invComponent_apply (n : ℕ) (pq : Finset.HasAntidiagonal.antidiagonal n)
    (z : (sectionsBicech p₁ p₂ πP 𝒰 𝒱 L M).X n) :
    invComponent hπ hP 𝒰 𝒱 L M hU hV hL hM n pq z =
      (HomologicalComplex.ιMapBifunctor (cechCochainComplex πX 𝒰 L) (cechCochainComplex πY 𝒱 M)
        (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℕ) pq.1.1 pq.1.2 n
        (Finset.HasAntidiagonal.mem_antidiagonal.1 pq.2)).hom
        ((cupFamEquiv hπ hP 𝒰 𝒱 L M hU hV hL hM pq.1.1 pq.1.2).symm
          (compLin' 𝒰 𝒱 L M pq.1.1 pq.1.2 (Finset.HasAntidiagonal.mem_antidiagonal.1 pq.2) z)) :=
  rfl

include hU hV hL hM in
/-- The degree-`n` inverse map, as a linear map. -/
def invLin (n : ℕ) :
    (sectionsBicech p₁ p₂ πP 𝒰 𝒱 L M).X n →ₗ[R] (totCech πX πY 𝒰 𝒱 L M).X n :=
  ∑ pq, invComponent hπ hP 𝒰 𝒱 L M hU hV hL hM n pq

include hU hV hL hM in
/-- The degree-`n` inverse map. -/
def sectionsInv (n : ℕ) : (sectionsBicech p₁ p₂ πP 𝒰 𝒱 L M).X n ⟶ (totCech πX πY 𝒰 𝒱 L M).X n :=
  ModuleCat.ofHom (X := (sectionsBicech p₁ p₂ πP 𝒰 𝒱 L M).X n)
    (Y := (totCech πX πY 𝒰 𝒱 L M).X n) (invLin hπ hP 𝒰 𝒱 L M hU hV hL hM n)

lemma cupFamEquiv_symm_cupFam (p q : ℕ)
    (x : ((curriedTensor (ModuleCat.{u} R)).obj ((cechCochainComplex πX 𝒰 L).X p)).obj
      ((cechCochainComplex πY 𝒱 M).X q)) :
    (cupFamEquiv hπ hP 𝒰 𝒱 L M hU hV hL hM p q).symm (cupFamT hπ hP 𝒰 𝒱 L M p q x) = x :=
  (cupFamEquiv hπ hP 𝒰 𝒱 L M hU hV hL hM p q).symm_apply_apply x

lemma cupFam_cupFamEquiv_symm (p q : ℕ)
    (c : ∀ (s : 𝒰.Idx p) (t : 𝒱.Idx q),
      (ofModules πP (extTensor p₁ p₂ L M)).obj (biOpen (prodBiCover p₁ p₂ 𝒰 𝒱) s t)) :
    cupFamT hπ hP 𝒰 𝒱 L M p q ((cupFamEquiv hπ hP 𝒰 𝒱 L M hU hV hL hM p q).symm c) = c :=
  (cupFamEquiv hπ hP 𝒰 𝒱 L M hU hV hL hM p q).apply_symm_apply c

lemma sectionsHom_invLin (n : ℕ) (z : (sectionsBicech p₁ p₂ πP 𝒰 𝒱 L M).X n) :
    (sectionsHom hπ hP 𝒰 𝒱 L M n).hom (invLin hπ hP 𝒰 𝒱 L M hU hV hL hM n z) = z := by
  have e1 : toΓ 𝒰 𝒱 L M
      ((sectionsHom hπ hP 𝒰 𝒱 L M n).hom (invLin hπ hP 𝒰 𝒱 L M hU hV hL hM n z)) =
      ∑ pq : Finset.HasAntidiagonal.antidiagonal n,
        insT (𝒲 := prodBiCover p₁ p₂ 𝒰 𝒱) (F := extTensor p₁ p₂ L M)
          (Finset.HasAntidiagonal.mem_antidiagonal.1 pq.2)
          (fun s t => compF (toΓ 𝒰 𝒱 L M z) pq.1.1 pq.1.2
            (Finset.HasAntidiagonal.mem_antidiagonal.1 pq.2) s t) := by
    rw [invLin, LinearMap.sum_apply, map_sum, toΓ_sum]
    refine Finset.sum_congr rfl fun pq _ => ?_
    rw [invComponent_apply, ι_sectionsHom_apply, cupFam_cupFamEquiv_symm]
    rfl
  change toΓ 𝒰 𝒱 L M _ = toΓ 𝒰 𝒱 L M z
  refine (compF_eq_iff (𝒲 := prodBiCover p₁ p₂ 𝒰 𝒱) (F := extTensor p₁ p₂ L M) _ _).2 ?_
  intro p' q' h' s' t'
  rw [e1, compF_sum,
    Fintype.sum_eq_single ⟨(p', q'), Finset.HasAntidiagonal.mem_antidiagonal.2 h'⟩]
  · exact compF_insT_self (𝒲 := prodBiCover p₁ p₂ 𝒰 𝒱) (F := extTensor p₁ p₂ L M) _ _ _ s' t'
  · intro pq hne
    exact compF_insT_ne (𝒲 := prodBiCover p₁ p₂ 𝒰 𝒱) (F := extTensor p₁ p₂ L M) _ _
      (fun e => hne (Subtype.ext e.symm)) _ s' t'

lemma invLin_insT (n p q : ℕ) (h : p + q = n)
    (x : ((curriedTensor (ModuleCat.{u} R)).obj ((cechCochainComplex πX 𝒰 L).X p)).obj
      ((cechCochainComplex πY 𝒱 M).X q)) :
    invLin hπ hP 𝒰 𝒱 L M hU hV hL hM n
        (ofΓ 𝒰 𝒱 L M (insT (𝒲 := prodBiCover p₁ p₂ 𝒰 𝒱) (F := extTensor p₁ p₂ L M) h
          (famΓ (cupFamT hπ hP 𝒰 𝒱 L M p q x)))) =
      (HomologicalComplex.ιMapBifunctor (cechCochainComplex πX 𝒰 L)
        (cechCochainComplex πY 𝒱 M) (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℕ)
        p q n h).hom x := by
  rw [invLin, LinearMap.sum_apply,
    Fintype.sum_eq_single ⟨(p, q), Finset.HasAntidiagonal.mem_antidiagonal.2 h⟩]
  · rw [invComponent_apply]
    have hc : compLin' (πP := πP) 𝒰 𝒱 L M p q h
        (ofΓ (πP := πP) 𝒰 𝒱 L M (insT h (famΓ (cupFamT hπ hP 𝒰 𝒱 L M p q x)))) =
          cupFamT hπ hP 𝒰 𝒱 L M p q x :=
      funext fun s => funext fun t =>
        compF_insT_self (𝒲 := prodBiCover p₁ p₂ 𝒰 𝒱) (F := extTensor p₁ p₂ L M) _ _ _ s t
    rw [hc, cupFamEquiv_symm_cupFam]
  · intro pq hne
    rw [invComponent_apply]
    have hc : compLin' (πP := πP) 𝒰 𝒱 L M pq.1.1 pq.1.2
        (Finset.HasAntidiagonal.mem_antidiagonal.1 pq.2)
        (ofΓ (πP := πP) 𝒰 𝒱 L M (insT h (famΓ (cupFamT hπ hP 𝒰 𝒱 L M p q x)))) = 0 :=
      funext fun s => funext fun t => by
        change compF (𝒲 := prodBiCover p₁ p₂ 𝒰 𝒱) (F := extTensor p₁ p₂ L M)
          (insT h (famΓ (cupFamT hπ hP 𝒰 𝒱 L M p q x))) pq.1.1 pq.1.2
          (Finset.HasAntidiagonal.mem_antidiagonal.1 pq.2) s t = _
        refine (compF_insT_ne (𝒲 := prodBiCover p₁ p₂ 𝒰 𝒱) (F := extTensor p₁ p₂ L M) h
          (Finset.HasAntidiagonal.mem_antidiagonal.1 pq.2) (fun e => hne (Subtype.ext e))
          (famΓ (cupFamT hπ hP 𝒰 𝒱 L M p q x)) s t).trans ?_
        rfl
    rw [hc, map_zero, map_zero]

lemma sectionsHom_comm (n : ℕ) :
    sectionsHom hπ hP 𝒰 𝒱 L M n ≫ (sectionsBicech p₁ p₂ πP 𝒰 𝒱 L M).d n (n + 1) =
      (totCech πX πY 𝒰 𝒱 L M).d n (n + 1) ≫ sectionsHom hπ hP 𝒰 𝒱 L M (n + 1) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  change p + q = n at h
  have h₁ : ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (p + 1, q) = n + 1 := by
    change p + 1 + q = n + 1
    omega
  have h₂ : ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (p, q + 1) = n + 1 := by
    change p + (q + 1) = n + 1
    omega
  rw [reassoc_of% (ι_sectionsHom hπ hP 𝒰 𝒱 L M n p q h), Functor.mapHomologicalComplex_obj_d,
    bicechComplex_d, HomologicalComplex.mapBifunctor.d_eq, Preadditive.add_comp,
    Preadditive.comp_add, HomologicalComplex.mapBifunctor.ι_D₁_assoc,
    HomologicalComplex.mapBifunctor.ι_D₂_assoc,
    HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (by simp : (ComplexShape.up ℕ).Rel p (p + 1))
      q (n + 1) h₁,
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ p (by simp : (ComplexShape.up ℕ).Rel q (q + 1))
      (n + 1) h₂]
  have hda : (cechCochainComplex πX 𝒰 L).d p (p + 1) =
      ModuleCat.ofHom ((ofModules πX L).d 𝒰 p) :=
    CochainComplex.of_d (V := ModuleCat.{u} R)
      (fun i => ModuleCat.of R ((ofModules πX L).cochain 𝒰 i))
      (fun i => ModuleCat.ofHom ((ofModules πX L).d 𝒰 i)) p
  have hdb : (cechCochainComplex πY 𝒱 M).d q (q + 1) =
      ModuleCat.ofHom ((ofModules πY M).d 𝒱 q) :=
    CochainComplex.of_d (V := ModuleCat.{u} R)
      (fun i => ModuleCat.of R ((ofModules πY M).cochain 𝒱 i))
      (fun i => ModuleCat.ofHom ((ofModules πY M).d 𝒱 i)) q
  rw [hda, hdb]
  refine ModuleCat.MonoidalCategory.tensor_ext fun a b => ?_
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, Units.smul_def, ModuleCat.hom_zsmul,
    LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_zsmul]
  have eε₁ : ((ComplexShape.ε₁ (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (p, q) : ℤˣ) : ℤ) = 1 := rfl
  have eε₂ : ((ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (p, q) : ℤˣ) : ℤ) = (-1) ^ p := by
    change (((-1 : ℤˣ) ^ p : ℤˣ) : ℤ) = (-1) ^ p
    simp
  rw [eε₁, eε₂, one_smul]
  have hH : horF (famΓ (𝒲 := prodBiCover p₁ p₂ 𝒰 𝒱) (π := πP) (cupFamT hπ hP 𝒰 𝒱 L M p q (a ⊗ₜ b))) =
      famΓ (𝒲 := prodBiCover p₁ p₂ 𝒰 𝒱) (π := πP) (cupFamT hπ hP 𝒰 𝒱 L M (p + 1) q ((ofModules πX L).d 𝒰 p a ⊗ₜ b)) := by
    have e1 : famΓ (𝒲 := prodBiCover p₁ p₂ 𝒰 𝒱) (π := πP) (cupFamT hπ hP 𝒰 𝒱 L M p q (a ⊗ₜ b)) = cupFamFun p₁ p₂ a b :=
      cupFam_tmul' hπ hP p q a b
    have e2 : famΓ (𝒲 := prodBiCover p₁ p₂ 𝒰 𝒱) (π := πP) (cupFamT hπ hP 𝒰 𝒱 L M (p + 1) q ((ofModules πX L).d 𝒰 p a ⊗ₜ b)) =
        cupFamFun p₁ p₂ (dΓ a) b := by
      refine (cupFam_tmul' hπ hP (p + 1) q _ b).trans ?_
      congr 1
      exact funext (d_eq_dΓ a)
    rw [e1, e2]
    funext s t
    exact horF_cupFamFun a b s t
  have hV' : verF (famΓ (𝒲 := prodBiCover p₁ p₂ 𝒰 𝒱) (π := πP) (cupFamT hπ hP 𝒰 𝒱 L M p q (a ⊗ₜ b))) =
      famΓ (𝒲 := prodBiCover p₁ p₂ 𝒰 𝒱) (π := πP) (cupFamT hπ hP 𝒰 𝒱 L M p (q + 1) (a ⊗ₜ (ofModules πY M).d 𝒱 q b)) := by
    have e1 : famΓ (𝒲 := prodBiCover p₁ p₂ 𝒰 𝒱) (π := πP) (cupFamT hπ hP 𝒰 𝒱 L M p q (a ⊗ₜ b)) = cupFamFun p₁ p₂ a b :=
      cupFam_tmul' hπ hP p q a b
    have e2 : famΓ (𝒲 := prodBiCover p₁ p₂ 𝒰 𝒱) (π := πP) (cupFamT hπ hP 𝒰 𝒱 L M p (q + 1) (a ⊗ₜ (ofModules πY M).d 𝒱 q b)) =
        cupFamFun p₁ p₂ a (dΓ' b) := by
      refine (cupFam_tmul' hπ hP p (q + 1) a _).trans ?_
      congr 1
      exact funext (d_eq_dΓ' b)
    rw [e1, e2]
    funext s t
    exact verF_cupFamFun a b s t
  have key := D_insT (prodBiCover p₁ p₂ 𝒰 𝒱) (extTensor p₁ p₂ L M) h
    (famΓ (𝒲 := prodBiCover p₁ p₂ 𝒰 𝒱) (π := πP) (cupFamT hπ hP 𝒰 𝒱 L M p q (a ⊗ₜ b)))
  rw [hH, hV'] at key
  refine key.trans ?_
  exact congrArg₂ (· + ·)
    (ι_sectionsHom_apply hπ hP 𝒰 𝒱 L M (n + 1) (p + 1) q h₁
      ((ofModules πX L).d 𝒰 p a ⊗ₜ b)).symm
    (congrArg (fun z => ((-1 : ℤ) ^ p) • z)
      (ι_sectionsHom_apply hπ hP 𝒰 𝒱 L M (n + 1) p (q + 1) h₂
        (a ⊗ₜ (ofModules πY M).d 𝒱 q b)).symm)

include hU hV hL hM in
/-- The tensor total complex of the Čech cochain complexes of the factors is isomorphic to the
complex of `R`-module global sections of the bi-Čech complex of `p₁^* L ⊗ p₂^* M`. -/
def sectionsIso : totCech πX πY 𝒰 𝒱 L M ≅ sectionsBicech p₁ p₂ πP 𝒰 𝒱 L M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n =>
      { hom := sectionsHom hπ hP 𝒰 𝒱 L M n
        inv := sectionsInv hπ hP 𝒰 𝒱 L M hU hV hL hM n
        hom_inv_id := by
          apply HomologicalComplex.mapBifunctor.hom_ext
          intro p q h
          rw [reassoc_of% (ι_sectionsHom hπ hP 𝒰 𝒱 L M n p q h), Category.comp_id]
          ext x
          exact invLin_insT hπ hP 𝒰 𝒱 L M hU hV hL hM n p q h x
        inv_hom_id := by
          ext z
          exact sectionsHom_invLin hπ hP 𝒰 𝒱 L M hU hV hL hM n z })
    (by
      rintro n _ rfl
      exact sectionsHom_comm hπ hP 𝒰 𝒱 L M n)

end Product

end Langlands.AlgebraicGeometry.Modules.BiCech
