import Langlands.GroupScheme.Reductive.SplitBorelPositiveIso
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Rational.SteinbergRootMapUniqueness

/-! # Positive root maps into the actual contracting group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.LocalSplitCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u}
  {G H : GroupScheme (Spec (CommRingCat.of R))}
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {ch : J → I → ℤ} {u : J → (Ga R ⟶ G)}

private theorem list_prod_comp_hom (f : H ⟶ G)
    {Z : Over (Spec (CommRingCat.of R))} (l : List (Z ⟶ H.X)) :
    l.prod ≫ f.hom.hom = (l.map (fun x => x ≫ f.hom.hom)).prod := by
  induction l with
  | nil => exact MonObj.one_comp _
  | cons x l ih =>
    simp only [List.prod_cons, List.map_cons, MonObj.mul_comp, ih]

/-- Root points commute with homomorphisms of their target group. -/
theorem rootPoint_comp_hom (a : Ga R ⟶ H) (f : H ⟶ G)
    (Z : Over (Spec (CommRingCat.of R))) (c : Γ(Z.left, ⊤)) :
    rootPoint a Z c ≫ f.hom.hom = rootPoint (a ≫ f) Z c := by
  simp only [rootPoint, Grp.comp_hom_hom, Category.assoc]

/-- Ordered multiplication commutes with homomorphisms of its target group. -/
theorem orderedProduct_comp_hom (a : J → (Ga R ⟶ H)) (f : H ⟶ G)
    {n : ℕ} (e : Fin n → J) (Z : Over (Spec (CommRingCat.of R)))
    (c : Fin n → Γ(Z.left, ⊤)) :
    orderedProduct a e Z c ≫ f.hom.hom =
      orderedProduct (fun k => a k ≫ f) e Z c := by
  simp only [orderedProduct, list_prod_comp_hom, List.map_ofFn,
    Function.comp_def, rootPoint_comp_hom]

/-- Every point of a positive-weight root map belongs to the contracting functor. -/
theorem rootPoint_mem_unipotent
    (hu : TorusEquivariant i ch u) (ν : I → ℤ) (a : J)
    (ha : 0 < coPairing (ch a) ν)
    (Z : Over (Spec (CommRingCat.of R))) (c : Γ(Z.left, ⊤)) :
    rootPoint (u a) Z c ∈
      (Dynamic.unipotent (AffineRegularBorel.cocharacter i ν)).carrier Z := by
  simpa only [orderedProduct, List.ofFn_succ, List.ofFn_zero,
    List.prod_cons, List.prod_nil, mul_one] using
    orderedProduct_mem_unipotent hu ν (fun _ : Fin 1 => a) (fun _ => ha) Z (fun _ => c)

/-- The whole all-test range of a positive root map lies in the contracting subgroup. -/
theorem range_root_le_unipotent
    (hu : TorusEquivariant i ch u) (ν : I → ℤ) (a : J)
    (ha : 0 < coPairing (ch a) ν) :
    SubgroupFunctor.range (u a) ≤
      Dynamic.unipotent (AffineRegularBorel.cocharacter i ν) := by
  rintro Z _ ⟨x, rfl⟩
  change x ≫ (u a).hom.hom ∈ _
  simpa only [rootPoint, VectorGroup.scalarPoint_coordinate] using
    rootPoint_mem_unipotent hu ν a ha Z
      ((VectorGroup.coordinates (CommRingCat.of R) 1 Z x).toAdd 0)

section Represented

variable {U : GroupScheme (Spec (CommRingCat.of R))} (j : U ⟶ G)
  (hu : TorusEquivariant i ch u) (ν : I → ℤ)
  (hU : (Dynamic.unipotent (AffineRegularBorel.cocharacter i ν)).IsRepresentedBy j)

/-- An actual additive-group homomorphism into the contracting representative. -/
def rootToUnipotent (a : J) (ha : 0 < coPairing (ch a) ν) : Ga R ⟶ U :=
  hU.factorHom (u a) (range_root_le_unipotent hu ν a ha)

/-- The factored root map recovers the original ambient homomorphism. -/
theorem rootToUnipotent_comp (a : J) (ha : 0 < coPairing (ch a) ν) :
    rootToUnipotent j hu ν hU a ha ≫ j = u a :=
  hU.factorHom_comp _ _

/-- The factorization is uniquely determined by its ambient composite. -/
theorem rootToUnipotent_unique (a : J) (ha : 0 < coPairing (ch a) ν)
    {f : Ga R ⟶ U} (hf : f ≫ j = u a) :
    f = rootToUnipotent j hu ν hU a ha :=
  hU.factorHom_unique _ _ hf

/-- Factoring a root map preserves its scalar points after the ambient inclusion. -/
theorem rootPoint_rootToUnipotent_comp (a : J) (ha : 0 < coPairing (ch a) ν)
    (Z : Over (Spec (CommRingCat.of R))) (c : Γ(Z.left, ⊤)) :
    rootPoint (rootToUnipotent j hu ν hU a ha) Z c ≫ j.hom.hom =
      rootPoint (u a) Z c := by
  rw [rootPoint_comp_hom, rootToUnipotent_comp]

variable {n : ℕ} {pos : Fin n → J}

/-- The ordered family of positive additive-group maps into the contracting group. -/
def positiveRootToUnipotent (hpos : ∀ k, 0 < coPairing (ch (pos k)) ν) :
    Fin n → (Ga R ⟶ U) :=
  fun k => rootToUnipotent j hu ν hU (pos k) (hpos k)

/-- Ordered products of the factored root maps recover the ambient ordered product. -/
theorem orderedProduct_positiveRootToUnipotent_comp
    (hpos : ∀ k, 0 < coPairing (ch (pos k)) ν)
    (Z : Over (Spec (CommRingCat.of R))) (c : Fin n → Γ(Z.left, ⊤)) :
    (List.ofFn fun k =>
      rootPoint (positiveRootToUnipotent j hu ν hU hpos k) Z (c k)).prod ≫ j.hom.hom =
      orderedProduct u pos Z c := by
  simp only [list_prod_comp_hom, List.map_ofFn, Function.comp_def, rootPoint_comp_hom,
    positiveRootToUnipotent, rootToUnipotent_comp, orderedProduct]

/-- The lifted chart is ordered multiplication inside the contracting group on every test. -/
theorem comp_positiveProductToUnipotent
    (hpos : ∀ k, 0 < coPairing (ch (pos k)) ν)
    {Z : Over (Spec (CommRingCat.of R))}
    (x : Z ⟶ (VectorGroup.groupScheme (CommRingCat.of R) n).X) :
    x ≫ positiveProductToUnipotent j hu ν hU hpos =
      (List.ofFn fun k => rootPoint (positiveRootToUnipotent j hu ν hU hpos k) Z
        ((VectorGroup.coordinates (CommRingCat.of R) n Z x).toAdd k)).prod := by
  let := hU.1
  apply (cancel_mono j.hom.hom).mp
  rw [Category.assoc, positiveProductToUnipotent_comp, comp_positiveProductMap,
    orderedProduct_positiveRootToUnipotent_comp]

variable [IsAffine U.X.left] {m : ℕ} {neg : Fin m → J}
  [IsOpenImmersion (cellMap i u neg pos).left]

/-- The positive-product scheme isomorphism has its ordered-product formula in `U`. -/
theorem comp_positiveProductIso_hom
    (hneg : ∀ k, coPairing (ch (neg k)) ν < 0)
    (hpos : ∀ k, 0 < coPairing (ch (pos k)) ν)
    {Z : Over (Spec (CommRingCat.of R))}
    (x : Z ⟶ (VectorGroup.groupScheme (CommRingCat.of R) n).X) :
    x ≫ (positiveProductIso j hu ν hU hneg hpos).hom =
      (List.ofFn fun k => rootPoint (positiveRootToUnipotent j hu ν hU hpos k) Z
        ((VectorGroup.coordinates (CommRingCat.of R) n Z x).toAdd k)).prod :=
  comp_positiveProductToUnipotent j hu ν hU hpos x

end Represented

end Langlands.GroupScheme.LocalSplitCell
