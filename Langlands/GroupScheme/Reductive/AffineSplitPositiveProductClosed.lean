import Langlands.GroupScheme.Reductive.SplitBorelPositiveIso
import Langlands.GroupScheme.Reductive.LocalSplitConeCommutator

/-! # Ordered products over positive roots are closed immersions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace LocalSplitCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u}
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G} {P : RootDatum J (I → ℤ) (I → ℤ)}
  {u : J → (Ga R ⟶ G)}

/-- The coordinate inclusion `𝔸ⁿ → 𝔸ⁿ⁺ⁿ'`, `x ↦ (x, 0)`. -/
def vectorPad (n n' : ℕ) :
    (VectorGroup.groupScheme (CommRingCat.of R) n).X ⟶
      (VectorGroup.groupScheme (CommRingCat.of R) (n + n')).X :=
  (VectorGroup.coordinates (CommRingCat.of R) (n + n') _).symm
    (Multiplicative.ofAdd (Fin.addCases
      (VectorGroup.coordinates (CommRingCat.of R) n _ (𝟙 _)).toAdd (fun _ => 0)))

/-- The coordinate projection `𝔸ⁿ⁺ⁿ' → 𝔸ⁿ` onto the first `n` coordinates. -/
def vectorTrunc (n n' : ℕ) :
    (VectorGroup.groupScheme (CommRingCat.of R) (n + n')).X ⟶
      (VectorGroup.groupScheme (CommRingCat.of R) n).X :=
  (VectorGroup.coordinates (CommRingCat.of R) n _).symm
    (Multiplicative.ofAdd fun k =>
      (VectorGroup.coordinates (CommRingCat.of R) (n + n') _ (𝟙 _)).toAdd (Fin.castAdd n' k))

theorem coordinates_vectorPad (n n' : ℕ) :
    (VectorGroup.coordinates (CommRingCat.of R) (n + n') _ (vectorPad (R := R) n n')).toAdd =
      Fin.addCases (VectorGroup.coordinates (CommRingCat.of R) n _ (𝟙 _)).toAdd (fun _ => 0) := by
  rw [vectorPad, MulEquiv.apply_symm_apply, toAdd_ofAdd]

theorem vectorPad_comp_vectorTrunc (n n' : ℕ) :
    vectorPad (R := R) n n' ≫ vectorTrunc n n' = 𝟙 _ := by
  apply VectorGroup.points_ext
  intro k
  rw [vectorTrunc, VectorGroup.coordinates_comp, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  have h := VectorGroup.coordinates_comp (vectorPad (R := R) n n') (𝟙 _)
  rw [Category.comp_id] at h
  have h' := congrFun h (Fin.castAdd n' k)
  dsimp only at h' ⊢
  rw [← h', coordinates_vectorPad]
  exact Fin.addCases_left _

omit [IsAffineHom G.X.hom] in
/-- Padding by zeros and multiplying over an enumeration beginning with `e` recovers the
ordered product over `e`. -/
theorem vectorPad_comp_positiveProductMap {n n' : ℕ} (posF : Fin (n + n') → J) (e : Fin n → J)
    (h : ∀ r, posF (Fin.castAdd n' r) = e r) :
    vectorPad (R := R) n n' ≫ positiveProductMap u posF = positiveProductMap u e := by
  rw [comp_positiveProductMap, coordinates_vectorPad,
    orderedProduct_initial u posF _ _ (fun j => by rw [Fin.addCases_right])]
  simp only [Fin.addCases_left, h]
  rfl

/-- The closed-immersion argument with the enumeration length as a free variable. -/
theorem isClosedImmersion_positiveProductMap_aux (hu : TorusEquivariant i (fun α => P.root α) u)
    {m n n' : ℕ} (neg : Fin m → J) (posF : Fin (n + n') → J)
    [IsOpenImmersion (cellMap i u neg posF).left] (ν : I → ℤ)
    (hneg : ∀ k, coPairing (P.root (neg k)) ν < 0)
    (hposF : ∀ k, 0 < coPairing (P.root (posF k)) ν) (e : Fin n → J)
    (h : ∀ r, posF (Fin.castAdd n' r) = e r) :
    IsClosedImmersion (positiveProductMap u e).left := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hpos_e : ∀ k, 0 < coPairing (P.root (e k)) ν := fun k => by
    rw [← h]
    exact hposF _
  let χ := AffineRegularBorel.cocharacter i ν
  let U := Dynamic.Affine.unipotentScheme χ
  let jU : U ⟶ G := Dynamic.Affine.unipotentHom χ
  have hU : (Dynamic.unipotent χ).IsRepresentedBy jU :=
    Dynamic.Affine.isRepresentedBy_unipotentHom χ
  have hUc : IsClosedSubgroup jU := Dynamic.Affine.isClosedSubgroup_unipotentHom χ
  have : IsClosedImmersion jU.hom.hom.left := hUc
  have : IsAffineHom U.X.hom := by
    rw [← Over.w jU.hom.hom]
    infer_instance
  have : IsAffine U.X.left := isAffine_of_isAffineHom U.X.hom
  have : Mono (positiveProductMap u posF) :=
    positiveProductMap_mono (i := i) (u := u) (neg := neg) (pos := posF)
  let s := positiveProductToUnipotent jU hu ν hU hpos_e
  have hs : s ≫ jU.hom.hom = positiveProductMap u e :=
    positiveProductToUnipotent_comp jU hu ν hU hpos_e
  let φ := positiveProductIso (neg := neg) (pos := posF) jU hu ν hU hneg hposF
  have hφ : φ.inv ≫ positiveProductMap u posF = jU.hom.hom :=
    positiveProductIso_inv_comp (neg := neg) (pos := posF) jU hu ν hU hneg hposF
  have hsφ : s ≫ φ.inv = vectorPad n n' := by
    apply (cancel_mono (positiveProductMap u posF)).mp
    rw [Category.assoc, hφ, hs, vectorPad_comp_positiveProductMap posF e h]
  have hsr : s ≫ (φ.inv ≫ vectorTrunc n n') = 𝟙 _ := by
    rw [← Category.assoc, hsφ, vectorPad_comp_vectorTrunc]
  have hid : IsClosedImmersion (s.left ≫ (φ.inv ≫ vectorTrunc n n').left) := by
    rw [← Over.comp_left, hsr, Over.id_left]
    infer_instance
  have : IsClosedImmersion s.left :=
    IsClosedImmersion.of_comp s.left (φ.inv ≫ vectorTrunc n n').left
  rw [← hs, Over.comp_left]
  infer_instance

/-- **Ordered products of distinct positive roots are closed immersions.** For a base `b` and an
injective family `e` of `b`-positive roots, the ordered product `w ↦ ∏ₖ u_{e k}(wₖ)` from
coordinate affine space to `G` is a closed immersion. It factors through the closed contracting
subgroup of a cocharacter positive on the positive roots, and there it has a retraction given by
the coordinates of a big cell whose positive enumeration begins with `e`. -/
theorem isClosedImmersion_positiveProductMap (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (hv : ∀ α, IsRootParametrization i (P.root α) (u α))
    (b : P.Base) {n : ℕ} (e : Fin n → J) (he : Function.Injective e)
    (hpos : ∀ k, b.IsPos (e k)) :
    IsClosedImmersion (positiveProductMap u e).left := by
  classical
  let L : List J := List.ofFn e
  have hL : L.Nodup := List.nodup_ofFn.mpr he
  have hLpos : ∀ x ∈ L, b.IsPos x := by
    intro x hx
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
    exact hpos k
  obtain ⟨m, n', neg, posF, hget, hopen, ν, hneg, hposF⟩ :=
    exists_cell_initial hG hmax hP hv b L hL hLpos
  have hu : TorusEquivariant i (fun α => P.root α) u := fun α Z t c => (hv α).equivariant Z t c
  have key : ∀ (k : ℕ) (hk : k = L.length) (posG : Fin (k + n') → J)
      [IsOpenImmersion (cellMap i u (fun k => (neg k : J)) posG).left],
      (∀ r, 0 < coPairing (P.root (posG r)) ν) →
      (∀ r : Fin k, posG (Fin.castAdd n' r) = L.get (Fin.cast hk r)) →
      IsClosedImmersion (positiveProductMap u e).left := by
    intro k hk posG _ hposG hgetG
    have hkn : k = n := hk.trans List.length_ofFn
    subst hkn
    exact isClosedImmersion_positiveProductMap_aux hu (fun k => (neg k : J)) posG ν hneg hposG e
      (fun r => by rw [hgetG]; simp [L])
  have : IsOpenImmersion (cellMap i u (fun k => (neg k : J)) (fun k => (posF k : J))).left :=
    hopen
  exact key L.length rfl (fun k => (posF k : J)) hposF (fun r => hget r)

end LocalSplitCell

end Langlands.GroupScheme
