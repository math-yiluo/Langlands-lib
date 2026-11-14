import Langlands.Geometry.Building.ChevalleyRootFiltrationBounds
import Langlands.Geometry.Building.SplitApartmentGaloisFixedPoint

/-! # Algebraic bounds on every split apartment filtration -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false

private instance splitBoundsAffine {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] :
    IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

section Orbit

variable {k : Type u} [Field k] [ValuativeRel k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {ω : kˣ → ℝ}

/-- Bounds at every depth for one family bound every filtration in its translation orbit. -/
theorem KPApartmentData.isAlgebraicallyBounded_filtration_of_orbit
    (D : KPApartmentData i ω) (φ : RootFunctionFamily S G)
    (hc : D.carrier = AddAction.orbit (V S) φ)
    (hB : ∀ a ∈ relativeRoots i, ∀ r : ℝ,
      IsAlgebraicallyBounded k G.X (rootFiltration i φ a r))
    (x : D.Apartment) (a : characterLattice S) (ha : a ∈ relativeRoots i) (r : ℝ) :
    IsAlgebraicallyBounded k G.X (D.filtration x a r : Set (rationalPoints G)) := by
  have hx := x.mem
  rw [hc] at hx
  obtain ⟨w, hw⟩ := hx
  change IsAlgebraicallyBounded k G.X (rootFiltration i x.val a r)
  rw [← hw, rootFiltration_vadd']
  exact hB a ha _

end Orbit

section Transport

variable {k : Type u} [Field k] [ValuativeRel k]
  {S S' : CommGroupScheme (Spec (CommRingCat.of k))}
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} {j : S'.toGrp ⟶ H}
  [Mono i.hom.hom.left] [Mono j.hom.hom.left]
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {ω : kˣ → ℝ}

/-- Actual cross-torus isomorphisms preserve bounds on every apartment filtration. -/
theorem KPApartmentData.isAlgebraicallyBounded_filtration_transport
    (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    (D : KPApartmentData i ω)
    (hB : ∀ (x : D.Apartment) a, a ∈ relativeRoots i → ∀ r : ℝ,
      IsAlgebraicallyBounded k G.X (D.filtration x a r : Set (rationalPoints G)))
    (x : (D.transport e f h).Apartment) (a : characterLattice S')
    (ha : a ∈ relativeRoots j) (r : ℝ) :
    IsAlgebraicallyBounded k H.X
      ((D.transport e f h).filtration x a r : Set (rationalPoints H)) := by
  obtain ⟨φ, hφ, hx⟩ := x.mem
  obtain ⟨a, rfl⟩ := (characterLattice.congr e).surjective a
  have ha' := (roots_mem_of_transport_iff e f h a).mp ha
  have hbound := (hB ⟨φ, hφ⟩ a ha' r).image f.hom.hom.hom
  change IsAlgebraicallyBounded k H.X (rootFiltration j x.val _ r)
  rw [← hx, ← image_rootFiltration_transport e f h]
  exact hbound

end Transport

namespace ChevalleyRootFamily

open Langlands.GroupScheme.SplitExistence Langlands.GroupScheme.SplitExistence.ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum J X Y} {b : P.Base} {D : ChevalleyData P b}
  {k : Type u} [Field k] [ValuativeRel k]
  (G : D.ChevGroup k) [Finite J] [P.IsReduced]
  [Module.Finite ℤ X] [Module.Free ℤ X]
  [IsAffine G.H.X.left] [LocallyOfFiniteType G.H.X.hom] [IsAffineHom G.H.X.hom]
  [Mono G.t.hom.hom.left]

/-- All points of the Chevalley apartment have bounded filtrations at all real depths,
provided nonzero scalars have additive values below every real threshold. -/
theorem isAlgebraicallyBounded_apartmentFiltration
    (omega : AddValuation k (WithTop ℝ)) (ω : kˣ → ℝ)
    (hω : ∀ x : kˣ, omega (x : k) = ((ω x : ℝ) : WithTop ℝ))
    (h3 : 3 ≤ (Set.range omega).encard)
    (hrel : ∀ x y : k, x ≤ᵥ y ↔ omega y ≤ omega x)
    (hscalar : ∀ r : ℝ, ∃ b : k, b ≠ 0 ∧ omega b ≤ (r : WithTop ℝ))
    (x : (apartmentData G omega ω hω h3).Apartment)
    (a : characterLattice (Tk (X := X) k)) (ha : a ∈ relativeRoots G.t) (r : ℝ) :
    IsAlgebraicallyBounded k G.H.X
      ((apartmentData G omega ω hω h3).filtration x a r : Set (rationalPoints G.H)) := by
  exact KPApartmentData.isAlgebraicallyBounded_filtration_of_orbit _ _ rfl
    (fun a ha r => isAlgebraicallyBounded_rootFiltration G omega hrel r (hscalar r) a ha)
    x a ha r

end ChevalleyRootFamily

section Split

open Langlands.GroupScheme.SplitExistence Langlands.GroupScheme.SplitExistence.ChevalleyData

/-- A split maximal torus admits apartment data with bounded filtrations at all points
and real depths, by transport from the actual Chevalley group. -/
theorem exists_bounded_kpApartmentData_of_isSplitTorus
    {k : Type u} [Field k] [ValuativeRel k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsSplitTorus T.toGrp)
    (j : T.toGrp ⟶ G) [Mono j.hom.hom.left] (hj : IsMaximalTorus j)
    (omega : AddValuation k (WithTop ℝ)) (ω : kˣ → ℝ)
    (hω : ∀ x : kˣ, omega (x : k) = ((ω x : ℝ) : WithTop ℝ))
    (h3 : 3 ≤ (Set.range omega).encard)
    (hrel : ∀ x y : k, x ≤ᵥ y ↔ omega y ≤ omega x)
    (hscalar : ∀ r : ℝ, ∃ b : k, b ≠ 0 ∧ omega b ≤ (r : WithTop ℝ)) :
    ∃ D : KPApartmentData j ω, ∀ (x : D.Apartment) a, a ∈ relativeRoots j →
      ∀ r : ℝ, IsAlgebraicallyBounded k G.X (D.filtration x a r : Set (rationalPoints G)) := by
  obtain ⟨J, hJ, P, hP, hred⟩ := rootDatumExistence k G hG T hT j hj
  have : Module.Finite ℤ (characterLattice T) := hT.finite_characterLattice
  have := isTorsionFree_weight P
  obtain ⟨b⟩ := nonempty_base_int P
  obtain ⟨DL⟩ := nonempty_chevalleyLieData P b
  let D : ChevalleyData P b := DL.toChevalleyData
  obtain ⟨Gc⟩ := D.nonempty_chevGroup k
  have : IsAffineHom Gc.H.X.hom := Gc.affine
  have : IsAffine Gc.H.X.left := isAffine_of_isAffineHom Gc.H.X.hom
  have : Smooth Gc.H.X.hom := Gc.smooth
  have hGcmax : IsMaximalTorus Gc.t := Gc.isMaximalTorus
  have : IsClosedImmersion Gc.t.hom.hom.left := hGcmax.2.1
  let Dc := ChevalleyRootFamily.apartmentData Gc omega ω hω h3
  let t : T ≅ Tk (X := characterLattice T) k :=
    hT.isoOfCharacterEquiv (isSplitTorus_Tk k P) (charEquiv k (X := characterLattice T))
  have hR : IsRootDatumOf (CommGroupScheme.groupHom t.hom ≫ Gc.t) P :=
    IsRootDatumOf.precomp_torusIso t Gc.isRootDatumOf hP.1 (chevDatumEquiv k P) fun χ => by
      rw [hT.character_congr_isoOfCharacterEquiv (isSplitTorus_Tk k P)]
      rfl
  have hM : IsMaximalTorus (CommGroupScheme.groupHom t.hom ≫ Gc.t) :=
    IsMaximalTorus.precomp_torusIso t hGcmax
  obtain ⟨ψ, hψ⟩ := splitCommonTorusIsomorphism k G Gc.H hG Gc.isConnectedReductive T hT j
    (CommGroupScheme.groupHom t.hom ≫ Gc.t) hj hM J J P P hP hR (Equiv.refl J) rfl rfl
  refine ⟨Dc.transport t.symm ψ.symm (torusTransport_inverse_square t ψ hψ), ?_⟩
  exact KPApartmentData.isAlgebraicallyBounded_filtration_transport _ _ _ Dc
    (ChevalleyRootFamily.isAlgebraicallyBounded_apartmentFiltration Gc omega ω hω h3 hrel hscalar)

/-- Every supplied split apartment has algebraically bounded filtrations at every point
and real depth, by the published uniqueness of split apartment classes. -/
theorem KPApartmentData.isAlgebraicallyBounded_filtration_of_isSplitTorus
    {k : Type u} [Field k] [ValuativeRel k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsSplitTorus T.toGrp)
    (j : T.toGrp ⟶ G) [Mono j.hom.hom.left] (hj : IsMaximalTorus j)
    (omega : AddValuation k (WithTop ℝ)) (ω : kˣ → ℝ)
    (hω : ∀ x : kˣ, omega (x : k) = ((ω x : ℝ) : WithTop ℝ))
    (h3 : 3 ≤ (Set.range omega).encard)
    (hrel : ∀ x y : k, x ≤ᵥ y ↔ omega y ≤ omega x)
    (hscalar : ∀ r : ℝ, ∃ b : k, b ≠ 0 ∧ omega b ≤ (r : WithTop ℝ))
    (D : KPApartmentData j ω) (x : D.Apartment)
    (a : characterLattice T) (ha : a ∈ relativeRoots j) (r : ℝ) :
    IsAlgebraicallyBounded k G.X (D.filtration x a r : Set (rationalPoints G)) := by
  obtain ⟨E, hE⟩ := exists_bounded_kpApartmentData_of_isSplitTorus G hG T hT j hj
    omega ω hω h3 hrel hscalar
  have hadd (s t : kˣ) : ω (s * t) = ω s + ω t := by
    have he := omega.map_mul (s : k) (t : k)
    rw [← Units.val_mul, hω, hω, hω, ← WithTop.coe_add, WithTop.coe_inj] at he
    exact he
  have he := KPApartmentData.eq_of_isMaximalTorus_of_isSplitTorus hG hT hj hadd D E
  subst D
  exact hE x a ha r

/-- Generic boundedness of all real-depth root filtrations in a supplied split apartment. -/
def SplitApartmentRootFiltrationBoundedStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (_hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (_hT : IsSplitTorus T.toGrp)
    (j : T.toGrp ⟶ G) [Mono j.hom.hom.left] (_hj : IsMaximalTorus j)
    (omega : AddValuation k (WithTop ℝ)) (ω : kˣ → ℝ)
    (_hω : ∀ x : kˣ, omega (x : k) = ((ω x : ℝ) : WithTop ℝ)),
    3 ≤ (Set.range omega).encard →
    (∀ x y : k, x ≤ᵥ y ↔ omega y ≤ omega x) →
    (∀ r : ℝ, ∃ b : k, b ≠ 0 ∧ omega b ≤ (r : WithTop ℝ)) →
    ∀ (D : KPApartmentData j ω) (x : D.Apartment) a, a ∈ relativeRoots j →
      ∀ r : ℝ, IsAlgebraicallyBounded k G.X (D.filtration x a r : Set (rationalPoints G))

/-- Chevalley coordinate bounds, transport and uniqueness prove the split statement. -/
theorem splitApartmentRootFiltrationBounded :
    SplitApartmentRootFiltrationBoundedStatement.{u} := by
  intro k _ _ G _ hG T hT j _ hj omega ω hω h3 hrel hscalar D x a ha r
  exact D.isAlgebraicallyBounded_filtration_of_isSplitTorus G hG T hT j hj
    omega ω hω h3 hrel hscalar x a ha r

end Split

end Langlands.Geometry.Building
