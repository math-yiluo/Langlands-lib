import Langlands.GroupScheme.Rational.ClassFunctionsDynamicLimits
import Langlands.GroupScheme.Rational.ClassFunctionsStronglyRegularFibresTransport
import Langlands.GroupScheme.Rational.ClassFunctionsBaseChange
import Langlands.GroupScheme.Rational.ClassFunctionsTorusSeparationStatement
import Langlands.GroupScheme.Absolute.BorelPointContainmentStatement
import Langlands.GroupScheme.Absolute.RegularCocharacterBorelProof
import Langlands.GroupScheme.Absolute.BorelMaximalTorusProof
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof
import Langlands.GroupScheme.Rational.MaximalTorusFiniteType
import Langlands.GroupScheme.Torus.SplittingAssembly
import Langlands.RingTheory.Coalgebra.SeparablyClosedGroupLikeSpanningProof

/-! # Strongly regular fibres of the canonical quotient over an algebraically closed field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ClassFunctions

/-- Geometric conjugacy in a fibre of the canonical class-function quotient of a semisimple
group over an algebraically closed field, through a point whose all-test centralizer lies in a
closed torus. This is the algebraically closed core consumed by
`stronglyRegularFibres_of_algClosed`. -/
def AlgClosedStronglyRegularFibresStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (H : GroupScheme (Spec (CommRingCat.of k))) (hH : IsSemisimple H),
    letI : IsAffineHom H.X.hom := hH.isConnectedReductive.isAffineHom
    ∀ (y w : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X)
      (S : GroupScheme (Spec (CommRingCat.of k))) (j : S ⟶ H),
      IsTorus S → IsClosedSubgroup j →
      (∀ {Z : Over (Spec (CommRingCat.of k))} (c : Z ⟶ H.X),
        c * (toUnit Z ≫ w) = (toUnit Z ≫ w) * c →
          ∃ s : Z ⟶ S.X, s ≫ j.hom.hom = c) →
      y ≫ rho H = w ≫ rho H →
      ∃ g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X,
        g * y * g⁻¹ = w

namespace AlgClosedFibres

variable {k : Type u} [Field k]

local notation "U₀" => 𝟙_ (Over (Spec (CommRingCat.of k)))

/-- Conjugation by a base point, on base points. -/
theorem comp_innerIso_hom_base {G : GroupScheme (Spec (CommRingCat.of k))}
    (g x : U₀ ⟶ G.X) : x ≫ (G.innerIso g).hom.hom.hom = g * x * g⁻¹ := by
  rw [comp_innerIso_hom]
  rfl

/-- A point lying in both the contracting subgroup and the centralizer of a cocharacter of a
separated group scheme is trivial. -/
theorem eq_one_of_mem_unipotent_of_mem_centralizer {S : Scheme.{u}} {G : GroupScheme S}
    [IsSeparated G.X.hom] (χ : (Gm S).toGrp ⟶ G) {T : Over S} {v : T ⟶ G.X}
    (hu : v ∈ (Dynamic.unipotent χ).carrier T) (hz : v ∈ (Dynamic.centralizer χ).carrier T) :
    v = 1 :=
  (Dynamic.hasLimit_of_mem_centralizer χ hz).unique χ hu

/-- A point of a closed torus of a smooth affine connected group over an algebraically closed
field is conjugate to a point of any given maximal torus. -/
theorem exists_conj_eq_comp_of_isTorus [IsAlgClosed k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [ConnectedSpace G.X.left]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {jT : T.toGrp ⟶ G}
    (hjT : IsMaximalTorus jT)
    {S : GroupScheme (Spec (CommRingCat.of k))} (j : S ⟶ G) (hS : IsTorus S)
    (hj : IsClosedSubgroup j) (s : U₀ ⟶ S.X) :
    ∃ (g : U₀ ⟶ G.X) (t : U₀ ⟶ T.X), g * (s ≫ j.hom.hom) * g⁻¹ = t ≫ jT.hom.hom := by
  let S₀ : CommGroupScheme (Spec (CommRingCat.of k)) := { S with comm := hS.isCommMonObj }
  obtain ⟨M, jM, hjM, f, hf⟩ :=
    exists_maximalTorus_extension_of_finiteType G (T := S₀) j hS hj
  obtain ⟨g, φ, hg⟩ := maximalTorusConjugacy k G M T jM jT hjM hjT
  refine ⟨g, s ≫ f.hom.hom ≫ (CommGroupScheme.groupHom φ.hom).hom.hom, ?_⟩
  rw [← comp_innerIso_hom_base, ← hf]
  have h := congrArg (fun ψ : M.toGrp ⟶ G => (s ≫ f.hom.hom) ≫ ψ.hom.hom) hg
  simpa only [Grp.comp_hom_hom, Category.assoc] using h

/-- Let `h * t * h⁻¹ = w`, where `t` is a point of a commutative subgroup `jT` and the all-test
centralizer of `w` lies in a commutative subgroup `j`. Then every base point commuting with
`t` centralizes `jT` on every test. -/
theorem mem_torusCentralizer_of_commute
    {G S : GroupScheme (Spec (CommRingCat.of k))} (j : S ⟶ G) [IsCommMonObj S.X]
    {w : U₀ ⟶ G.X}
    (hC : ∀ {Z : Over (Spec (CommRingCat.of k))} (c : Z ⟶ G.X),
        c * (toUnit Z ≫ w) = (toUnit Z ≫ w) * c → ∃ s : Z ⟶ S.X, s ≫ j.hom.hom = c)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (jT : T.toGrp ⟶ G)
    {h : U₀ ⟶ G.X} {t₀ : U₀ ⟶ T.X} (ht : h * (t₀ ≫ jT.hom.hom) * h⁻¹ = w)
    {v : U₀ ⟶ G.X} (hv : v * (t₀ ≫ jT.hom.hom) = (t₀ ≫ jT.hom.hom) * v) :
    v ∈ (torusCentralizer jT).carrier U₀ := by
  intro V a c
  have ha : a = toUnit V := toUnit_unique _ _
  subst ha
  -- the conjugate of a point commuting with the restriction of `t` commutes with `w`
  have key : ∀ x : V ⟶ G.X, x * (toUnit V ≫ t₀ ≫ jT.hom.hom) = (toUnit V ≫ t₀ ≫ jT.hom.hom) * x →
      ∃ s : V ⟶ S.X, s ≫ j.hom.hom = (toUnit V ≫ h) * x * (toUnit V ≫ h)⁻¹ := by
    intro x hx
    apply hC
    rw [← ht, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv]
    have := ((Commute.conj_iff (toUnit V ≫ h)).mpr hx).eq
    simpa only [mul_assoc] using this
  have hx : (toUnit V ≫ v) * (toUnit V ≫ t₀ ≫ jT.hom.hom) =
      (toUnit V ≫ t₀ ≫ jT.hom.hom) * (toUnit V ≫ v) := by
    rw [← MonObj.comp_mul, ← MonObj.comp_mul, hv]
  have hy : (c ≫ jT.hom.hom) * (toUnit V ≫ t₀ ≫ jT.hom.hom) =
      (toUnit V ≫ t₀ ≫ jT.hom.hom) * (c ≫ jT.hom.hom) := by
    rw [← Category.assoc, ← MonObj.mul_comp, ← MonObj.mul_comp, mul_comm]
  obtain ⟨sx, hsx⟩ := key _ hx
  obtain ⟨sy, hsy⟩ := key _ hy
  have hs : (sx ≫ j.hom.hom) * (sy ≫ j.hom.hom) = (sy ≫ j.hom.hom) * (sx ≫ j.hom.hom) := by
    rw [← MonObj.mul_comp, ← MonObj.mul_comp, mul_comm]
  rw [hsx, hsy] at hs
  exact (Commute.conj_iff (toUnit V ≫ h)).mp hs

end AlgClosedFibres

open AlgClosedFibres in
/-- **The algebraically closed core from its inputs.** `hP1` places a point in a Borel subgroup,
`hP2` separates conjugacy classes of maximal-torus points by the canonical quotient, and `hR4`
is the Ax–Grothendieck conjugation lemma on the contracting subgroup of a cocharacter. -/
theorem algClosedStronglyRegularFibres_of
    (hP1 : BorelPointContainmentStatement.{u}) (hP2 : TorusSeparationStatement.{u})
    (hR4 : ∀ {k : Type u} [Field k] [IsAlgClosed k] {G : GroupScheme (Spec (CommRingCat.of k))}
      [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
      (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
      {t : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X},
      t ∈ (Dynamic.centralizer χ).carrier (𝟙_ _) →
      (∀ v ∈ (Dynamic.unipotent χ).carrier (𝟙_ _), v * t = t * v → v = 1) →
      ∀ {u : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X},
        u ∈ (Dynamic.unipotent χ).carrier (𝟙_ _) →
        ∃ v ∈ (Dynamic.unipotent χ).carrier (𝟙_ _), v * t * v⁻¹ = u * t) :
    AlgClosedStronglyRegularFibresStatement.{u} := by
  intro k _ _ H hH
  let : IsAffineHom H.X.hom := hH.isConnectedReductive.isAffineHom
  intro y w S j hS hj hC hrho
  have hG := hH.isConnectedReductive
  have : Smooth H.X.hom := hG.smooth
  have : ConnectedSpace H.X.left := hG.connectedSpace
  have : IsCommMonObj S.X := hS.isCommMonObj
  -- `y` lies in a Borel subgroup, which contains a split maximal torus
  obtain ⟨B, i, b, hB, hb⟩ := hP1 k H y
  obtain ⟨T, jT, -, hjT, f, hf⟩ := borelMaximalTorus k H B i hB
  have hTs : IsSplitTorus T.toGrp :=
    SplittingAssembly.isSplit_of_isSepClosed_of_prerequisites
      CoalgebraDescent.separablyClosedGroupLikeSpanning T.toGrp hjT.1
  obtain ⟨ν, hν, hrep⟩ := (regularCocharacterBorel k H hG T jT hTs hjT).2.2 B i f hB hf
  let χ := CommGroupScheme.groupHom ν ≫ jT
  have hy : y ∈ (Dynamic.parabolic χ).carrier (𝟙_ _) := by
    rw [← hrep.2]
    exact ⟨b, hb⟩
  have hZ := centralizer_comp_eq_range_of_isRegular hG hTs jT hjT ν hν
  -- the limit `t` of `y` lies in `T` and has the quotient image of `y`
  let t := Dynamic.limit χ ⟨y, hy⟩
  have ht : t ∈ (Dynamic.centralizer χ).carrier (𝟙_ _) := Dynamic.limit_mem_centralizer χ _
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ T.X,
      t₀ ≫ jT.hom.hom = t := by
    have h := ht
    rw [hZ] at h
    exact h
  have hrho_t : t ≫ rho H = w ≫ rho H := (rho_limit H χ ⟨y, hy⟩).symm.trans hrho
  -- `w` lies in `S`, hence is conjugate to a point of `T`
  obtain ⟨s₀, hs₀⟩ := hC w (by rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp])
  obtain ⟨g₁, w₀, hg₁⟩ := exists_conj_eq_comp_of_isTorus hjT j hS hj s₀
  rw [hs₀] at hg₁
  -- separation of the two points of `T`
  have hsep : (t₀ ≫ jT.hom.hom) ≫ rho H = (w₀ ≫ jT.hom.hom) ≫ rho H := by
    rw [ht₀, hrho_t, ← hg₁, rho_conjugation]
  obtain ⟨g₂, hg₂⟩ := hP2 k H hH T jT hjT t₀ w₀ hsep
  -- `h := g₁⁻¹ * g₂` conjugates `t` to `w`
  have hh : (g₁⁻¹ * g₂) * (t₀ ≫ jT.hom.hom) * (g₁⁻¹ * g₂)⁻¹ = w := by
    calc (g₁⁻¹ * g₂) * (t₀ ≫ jT.hom.hom) * (g₁⁻¹ * g₂)⁻¹
        = g₁⁻¹ * (g₂ * (t₀ ≫ jT.hom.hom) * g₂⁻¹) * g₁ := by group
      _ = w := by rw [hg₂, ← hg₁]; group
  -- points of the contracting subgroup commuting with `t` are trivial
  have hfree : ∀ v ∈ (Dynamic.unipotent χ).carrier (𝟙_ _), v * t = t * v → v = 1 := by
    intro v hvU hvt
    rw [← ht₀] at hvt
    have hvT := mem_torusCentralizer_of_commute j hC jT hh hvt
    rw [maximalTorusCentralizer k H hG T jT hjT, ← hZ] at hvT
    exact eq_one_of_mem_unipotent_of_mem_centralizer χ hvU hvT
  -- Ax–Grothendieck: `y = v * t * v⁻¹` for a point `v` of the contracting subgroup
  obtain ⟨v, -, hv⟩ := hR4 χ ht hfree (Dynamic.mul_inv_limit_mem_unipotent χ ⟨y, hy⟩)
  rw [inv_mul_cancel_right] at hv
  replace hv : v * t * v⁻¹ = y := hv
  rw [ht₀] at hh
  refine ⟨(g₁⁻¹ * g₂) * v⁻¹, ?_⟩
  rw [← hv, ← hh]
  group

/-- **The target from the three inputs.** The published field transport and field base change
reduce `StronglyRegularFibresStatement` to the algebraically closed core. -/
theorem stronglyRegularFibres_of_inputs
    (hP1 : BorelPointContainmentStatement.{u}) (hP2 : TorusSeparationStatement.{u})
    (hR4 : ∀ {k : Type u} [Field k] [IsAlgClosed k] {G : GroupScheme (Spec (CommRingCat.of k))}
      [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
      (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
      {t : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X},
      t ∈ (Dynamic.centralizer χ).carrier (𝟙_ _) →
      (∀ v ∈ (Dynamic.unipotent χ).carrier (𝟙_ _), v * t = t * v → v = 1) →
      ∀ {u : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X},
        u ∈ (Dynamic.unipotent χ).carrier (𝟙_ _) →
        ∃ v ∈ (Dynamic.unipotent χ).carrier (𝟙_ _), v * t * v⁻¹ = u * t) :
    StronglyRegularFibresStatement.{u} :=
  stronglyRegularFibres_of_algClosed fieldBaseChange
    (algClosedStronglyRegularFibres_of hP1 hP2 hR4)

end Langlands.GroupScheme.ClassFunctions
