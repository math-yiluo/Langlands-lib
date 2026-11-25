import Langlands.Cohomology.Profinite.Comparison.FiniteQuotients
import Langlands.Cohomology.Profinite.Cup.Functoriality
import Langlands.Cohomology.Tate.OrdinaryCupDefinitions

noncomputable section

namespace Langlands.ProfiniteCohomology

open CategoryTheory MonoidalCategory TensorProduct

universe u

/-! ### The cup product on the cohomology of an abstract group

`GroupCoh.cupH` is the Library's `Langlands.Tate.ordinaryCup` for the tensor pairing, read in
degree `n = p + q`; its cocycle-level description `GroupCoh.cupCocycles` uses `cupCochain`. -/

namespace GroupCoh

open groupCohomology

variable {k G : Type u} [CommRing k] [Group G] {A B : Rep k G} {p q n : ℕ}

theorem cocycles_ext {z z' : groupCohomology.cocycles A n} (h : iCocycles A n z = iCocycles A n z') : z = z' :=
  (ModuleCat.mono_iff_injective _).1 inferInstance h

theorem d_iCocycles (z : groupCohomology.cocycles A n) :
    (inhomogeneousCochains.d A n).hom (iCocycles A n z) = 0 := by
  have h := congr(($((inhomogeneousCochains A).iCycles_d n (n + 1))).hom z)
  simpa using h

theorem d_cupCochain_iCocycles (h : p + q = n) (z : groupCohomology.cocycles A p) (w : groupCohomology.cocycles B q) :
    (inhomogeneousCochains.d (A ⊗ B) n).hom (cupCochain h (iCocycles A p z) (iCocycles B q w)) =
      0 := by
  rw [d_cupCochain, d_iCocycles, d_iCocycles, cupCochain_zero_left, cupCochain_zero_right,
    smul_zero, add_zero]

/-- The cup product of two cocycles of an abstract group, by `cupCochain`. -/
def cupCocycle (h : p + q = n) (z : groupCohomology.cocycles A p) (w : groupCohomology.cocycles B q) : groupCohomology.cocycles (A ⊗ B) n :=
  cocyclesMk (cupCochain h (iCocycles A p z) (iCocycles B q w)) (d_cupCochain_iCocycles h z w)

theorem iCocycles_cupCocycle (h : p + q = n) (z : groupCohomology.cocycles A p) (w : groupCohomology.cocycles B q) :
    iCocycles (A ⊗ B) n (cupCocycle h z w) = cupCochain h (iCocycles A p z) (iCocycles B q w) :=
  iCocycles_mk _ (d_cupCochain_iCocycles h z w)

/-- The cup product of cocycles, as a bilinear map. -/
def cupCocycles (h : p + q = n) : groupCohomology.cocycles A p →ₗ[k] groupCohomology.cocycles B q →ₗ[k] groupCohomology.cocycles (A ⊗ B) n :=
  LinearMap.mk₂ k (cupCocycle h)
    (fun z z' w => cocycles_ext (by
      rw [map_add, iCocycles_cupCocycle, iCocycles_cupCocycle, iCocycles_cupCocycle, map_add]
      exact (cupₗ h).map_add₂ _ _ _))
    (fun c z w => cocycles_ext (by
      rw [map_smul, iCocycles_cupCocycle, iCocycles_cupCocycle, map_smul]
      exact (cupₗ h).map_smul₂ _ _ _))
    (fun z w w' => cocycles_ext (by
      rw [map_add, iCocycles_cupCocycle, iCocycles_cupCocycle, iCocycles_cupCocycle, map_add]
      exact (cupₗ h _).map_add _ _))
    (fun c z w => cocycles_ext (by
      rw [map_smul, iCocycles_cupCocycle, iCocycles_cupCocycle, map_smul]
      exact (cupₗ h _).map_smul _ _))

theorem iCocycles_cupCocycles (h : p + q = n) (z : groupCohomology.cocycles A p) (w : groupCohomology.cocycles B q) :
    iCocycles (A ⊗ B) n (cupCocycles h z w) = cupCochain h (iCocycles A p z) (iCocycles B q w) :=
  iCocycles_cupCocycle h z w

/-- The cup product `Hᵖ(G, A) × H^q(G, B) → Hⁿ(G, A ⊗ B)` of an abstract group, `p + q = n`: the
Library's `Langlands.Tate.ordinaryCup` for the tensor pairing, transported to degree `n`. -/
def cupH (h : p + q = n) :
    groupCohomology A p →ₗ[k] groupCohomology B q →ₗ[k] groupCohomology (A ⊗ B) n :=
  (Langlands.Tate.ordinaryCup (Langlands.Tate.tensorPairing A B) p q).compr₂
    (eqToHom (congrArg (groupCohomology (A ⊗ B)) h)).hom

theorem cupH_π (h : p + q = n) (z : groupCohomology.cocycles A p) (w : groupCohomology.cocycles B q) :
    cupH h (π A p z) (π B q w) = π (A ⊗ B) n (cupCocycles h z w) := by
  subst h
  rw [cupH, LinearMap.compr₂_apply, Langlands.Tate.ordinaryCup_π_π, eqToHom_refl,
    ModuleCat.hom_id, LinearMap.id_apply]
  refine congrArg (π (A ⊗ B) (p + q)) ?_
  apply cocycles_ext
  rw [Langlands.Tate.i_ordinaryCupCocycles, iCocycles_cupCocycles]
  rfl

theorem map_π_apply {A' : Rep k G} (φ : A ⟶ A') (z : groupCohomology.cocycles A n) :
    groupCohomology.map (MonoidHom.id G) φ n (π A n z) = π A' n (groupCohomology.cocyclesMap (MonoidHom.id G) φ n z) := by
  change (π A n ≫ groupCohomology.map (MonoidHom.id G) φ n).hom z =
    (groupCohomology.cocyclesMap (MonoidHom.id G) φ n ≫ π A' n).hom z
  rw [π_map]

theorem iCocycles_cocyclesMap {A' : Rep k G} (φ : A ⟶ A') (z : groupCohomology.cocycles A n) :
    iCocycles A' n (groupCohomology.cocyclesMap (MonoidHom.id G) φ n z) =
      fun x => φ.hom (iCocycles A n z x) := by
  change (groupCohomology.cocyclesMap (MonoidHom.id G) φ n ≫ iCocycles A' n).hom z = _
  rw [HomologicalComplex.cyclesMap_i]
  rfl

theorem map_cupH {A' B' : Rep k G} (φ : A ⟶ A') (ψ : B ⟶ B') (h : p + q = n)
    (a : groupCohomology A p) (b : groupCohomology B q) :
    groupCohomology.map (MonoidHom.id G) (φ ⊗ₘ ψ) n (cupH h a b) =
      cupH h (groupCohomology.map (MonoidHom.id G) φ p a) (groupCohomology.map (MonoidHom.id G) ψ q b) := by
  refine groupCohomology_induction_on a fun z => ?_
  refine groupCohomology_induction_on b fun w => ?_
  have key : groupCohomology.cocyclesMap (A := A ⊗ B) (MonoidHom.id G) (φ ⊗ₘ ψ) n (cupCocycles h z w) =
      cupCocycles h (groupCohomology.cocyclesMap (MonoidHom.id G) φ p z) (groupCohomology.cocyclesMap (MonoidHom.id G) ψ q w) := by
    refine cocycles_ext ?_
    rw [iCocycles_cocyclesMap, iCocycles_cupCocycles, iCocycles_cupCocycles, iCocycles_cocyclesMap,
      iCocycles_cocyclesMap]
    funext x
    exact tensorHom_cupCochain φ ψ h _ _ x
  rw [cupH_π, map_π_apply, map_π_apply, cupH_π, ← key]
  exact map_π_apply _ _

end GroupCoh

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Comparison

variable {A B : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B] {p q n : ℕ}

theorem toGroupCohomology_cohomologyπ (x : cocycles A p) :
    toGroupCohomology A p (cohomologyπ A p x) =
      groupCohomology.π A p (HomologicalComplex.cyclesMap (cochainsι A) p x) :=
  ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality (cochainsι A) p) x

theorem iCocycles_cyclesMap_cochainsι (x : cocycles A p) :
    groupCohomology.iCocycles A p (HomologicalComplex.cyclesMap (cochainsι A) p x) =
      cochainOf A (cocycleι A p x) :=
  ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i (cochainsι A) p) x

end Comparison

section Levels

variable (U : OpenNormalSubgroup G) {p q n : ℕ}

theorem inflation_π (A : Rep.{u} k G) [IsSmoothRep A]
    (z : groupCohomology.cocycles (A.quotientToInvariants U.toSubgroup) p) :
    inflation A U p (groupCohomology.π _ p z) =
      cohomologyπ A p (HomologicalComplex.cyclesMap (inflationCochains A U) p z) :=
  ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality (inflationCochains A U) p) z

theorem cochainOf_cocycleι_cyclesMap_inflationCochains (A : Rep.{u} k G) [IsSmoothRep A]
    (z : groupCohomology.cocycles (A.quotientToInvariants U.toSubgroup) p) :
    cochainOf A (cocycleι A p (HomologicalComplex.cyclesMap (inflationCochains A U) p z)) =
      fun g => (groupCohomology.iCocycles (A.quotientToInvariants U.toSubgroup) p z
        (fun i => (g i : G ⧸ U.toSubgroup)) : A) :=
  congrArg (fun ψ => cochainOf A (ψ.hom z))
    (HomologicalComplex.cyclesMap_i (inflationCochains A U) p)

theorem inflationCochains_comp_cochainsMap {A A' : Rep.{u} k G} [IsSmoothRep A]
    [IsSmoothRep A'] (f : A ⟶ A') :
    inflationCochains A U ≫ coeffCochainsMap f =
      groupCohomology.cochainsMap (MonoidHom.id _)
        ((Rep.quotientToInvariantsFunctor k U.toSubgroup).map f) ≫ inflationCochains A' U := by
  ext n x : 3
  rfl

theorem inflation_comp_cohomologyMap {A A' : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep A']
    (f : A ⟶ A') (n : ℕ) :
    inflation A U n ≫ coeffMap f n =
      groupCohomology.map (MonoidHom.id _)
        ((Rep.quotientToInvariantsFunctor k U.toSubgroup).map f) n ≫ inflation A' U n := by
  have h := congrArg (fun φ => HomologicalComplex.homologyMap φ n)
    (inflationCochains_comp_cochainsMap U f)
  simp only [HomologicalComplex.homologyMap_comp] at h
  exact h

theorem cohomologyMap_inflation {A A' : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep A']
    (f : A ⟶ A') (x : groupCohomology (A.quotientToInvariants U.toSubgroup) n) :
    coeffMap f n (inflation A U n x) =
      inflation A' U n (groupCohomology.map (MonoidHom.id _)
        ((Rep.quotientToInvariantsFunctor k U.toSubgroup).map f) n x) :=
  ConcreteCategory.congr_hom (inflation_comp_cohomologyMap U f n) x

variable (A B : Rep.{u} k G) [IsSmoothRep A] [IsSmoothRep B]

theorem cup_inflation (h : p + q = n)
    (x : groupCohomology (A.quotientToInvariants U.toSubgroup) p)
    (y : groupCohomology (B.quotientToInvariants U.toSubgroup) q) :
    cup h (inflation A U p x) (inflation B U q y) =
      inflation (A ⊗ B) U n (groupCohomology.map (MonoidHom.id _)
        (invariantsTensorHom A B U.toSubgroup) n (GroupCoh.cupH h x y)) := by
  refine groupCohomology_induction_on x fun x => ?_
  refine groupCohomology_induction_on y fun y => ?_
  rw [inflation_π, inflation_π, cup_cohomologyπ, GroupCoh.cupH_π,
    GroupCoh.map_π_apply, inflation_π]
  congr 1
  apply cocycles_ext
  rw [cocycleι_cupCocycles, cochainOf_cupLocallyConstant,
    cochainOf_cocycleι_cyclesMap_inflationCochains, cochainOf_cocycleι_cyclesMap_inflationCochains,
    cochainOf_cocycleι_cyclesMap_inflationCochains, GroupCoh.iCocycles_cocyclesMap,
    GroupCoh.iCocycles_cupCocycles]
  funext g
  simp only [cupCochain_apply]
  have hP : Fin.partialProd (fun i => (g i : G ⧸ U.toSubgroup)) ⟨p, by omega⟩ =
      ((Fin.partialProd g ⟨p, by omega⟩ : G) : G ⧸ U.toSubgroup) :=
    partialProd_comp_monoidHom (QuotientGroup.mk' U.toSubgroup) g _
  rw [hP]
  rfl

end Levels

end Langlands.ProfiniteCohomology
