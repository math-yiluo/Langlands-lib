import Langlands.VirtualRepresentation.Weil.Realization
import Langlands.VirtualRepresentation.ExactInduction
import Langlands.VirtualRepresentation.ExactRestriction
import Langlands.Weil.Representation.ContinuityProof
import Langlands.Weil.Representation.InductionContinuity

/-!
# Inflation from a finite quotient to continuous exact virtual groups

A homomorphism `π : G →* Q` with open kernel inflates finite-dimensional
representations of `Q` to continuous representations of `G`. On the split
Grothendieck group of `Q` this gives an integer-linear map to the continuous
exact virtual group of `G`. Coinduction from a subgroup `S` of `Q` inflates to
coinduction from its preimage.
-/

noncomputable section

universe uG uQ uV

namespace Langlands.FiniteRep

section CoindInflation

variable {k : Type*} [CommRing k] {G Q : Type*} [Group G] [Group Q]
  {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
variable (π : G →* Q) (S : Subgroup Q) (T : Subgroup G) (hT : ∀ g, g ∈ T ↔ π g ∈ S)
  (σ : Representation k S V) (τ : Representation k T W) (e : V ≃ₗ[k] W)
  (he : ∀ (t : T) (v : V), e (σ ⟨π t, (hT t).mp t.2⟩ v) = τ t (e v))

include he in
/-- An element of `T` in the kernel of `π` acts trivially through `τ`. -/
theorem coindInflation_tau_eq (t : T) (ht : π t = 1) (w : W) : τ t w = w := by
  have h1 : (⟨π t, (hT t).mp t.2⟩ : S) = 1 := Subtype.ext ht
  have h := he t (e.symm w)
  rw [h1, map_one, Module.End.one_apply, LinearEquiv.apply_symm_apply] at h
  exact h.symm

include he in
/-- Coinduced functions from `T` are constant on the fibres of `π`. -/
theorem coindInflation_apply_eq (F : Representation.coindV T.subtype τ) {g g' : G}
    (h : π g = π g') : F.1 g = F.1 g' := by
  have hmem : g' * g⁻¹ ∈ T := (hT _).mpr (by
    rw [map_mul, map_inv, ← h, mul_inv_cancel]
    exact S.one_mem)
  have hF := F.2 ⟨g' * g⁻¹, hmem⟩ g
  change F.1 (g' * g⁻¹ * g) = τ ⟨g' * g⁻¹, hmem⟩ (F.1 g) at hF
  rw [inv_mul_cancel_right] at hF
  rw [hF, coindInflation_tau_eq π S T hT σ τ e he ⟨g' * g⁻¹, hmem⟩
    (by rw [map_mul, map_inv, ← h, mul_inv_cancel])]

variable (hπ : Function.Surjective π)

/-- Composition with `π` and the linear equivalence `e` identifies the inflated
coinduced space from `S` with the coinduced space from `T`. -/
def coindInflationLinearEquiv :
    Representation.coindV S.subtype σ ≃ₗ[k] Representation.coindV T.subtype τ where
  toFun f := ⟨fun g => e (f.1 (π g)), by
    intro t g
    have hf := f.2 ⟨π t, (hT t).mp t.2⟩ (π g)
    change f.1 (π t * π g) = σ ⟨π t, (hT t).mp t.2⟩ (f.1 (π g)) at hf
    change e (f.1 (π ((t : G) * g))) = τ t (e (f.1 (π g)))
    rw [map_mul, hf, he]⟩
  invFun F := ⟨fun q => e.symm (F.1 (Function.surjInv hπ q)), by
    intro s q
    have hsT : Function.surjInv hπ (s : Q) ∈ T :=
      (hT _).mpr (by rw [Function.surjInv_eq hπ]; exact s.2)
    let t : T := ⟨Function.surjInv hπ (s : Q), hsT⟩
    change e.symm (F.1 (Function.surjInv hπ ((s : Q) * q))) =
      σ s (e.symm (F.1 (Function.surjInv hπ q)))
    have h1 : F.1 (Function.surjInv hπ ((s : Q) * q)) =
        F.1 ((t : G) * Function.surjInv hπ q) :=
      coindInflation_apply_eq π S T hT σ τ e he F (by
        rw [map_mul, Function.surjInv_eq hπ, Function.surjInv_eq hπ,
          Function.surjInv_eq hπ])
    have h2 := F.2 t (Function.surjInv hπ q)
    change F.1 ((t : G) * Function.surjInv hπ q) =
      τ t (F.1 (Function.surjInv hπ q)) at h2
    have hs : (⟨π t, (hT t).mp t.2⟩ : S) = s := Subtype.ext (Function.surjInv_eq hπ _)
    have h3 := he t (e.symm (F.1 (Function.surjInv hπ q)))
    rw [hs, LinearEquiv.apply_symm_apply] at h3
    rw [h1, h2, ← h3, LinearEquiv.symm_apply_apply]⟩
  left_inv f := by
    apply Subtype.ext
    funext q
    change e.symm (e (f.1 (π (Function.surjInv hπ q)))) = f.1 q
    rw [LinearEquiv.symm_apply_apply, Function.surjInv_eq hπ]
  right_inv F := by
    apply Subtype.ext
    funext g
    change e (e.symm (F.1 (Function.surjInv hπ (π g)))) = F.1 g
    rw [LinearEquiv.apply_symm_apply]
    exact coindInflation_apply_eq π S T hT σ τ e he F (Function.surjInv_eq hπ _)
  map_add' f f' := by
    apply Subtype.ext
    funext g
    exact map_add e _ _
  map_smul' c f := by
    apply Subtype.ext
    funext g
    exact map_smul e c _

/-- Inflation of coinduction from `S` along a surjection `π` is coinduction from
the preimage `T`, up to the coefficient equivalence `e`. -/
def coindInflationEquiv :
    Representation.Equiv ((Representation.coind S.subtype σ).comp π)
      (Representation.coind T.subtype τ) :=
  Representation.Equiv.mk (coindInflationLinearEquiv π S T hT σ τ e he hπ) (by
    intro g
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext x
    change e (f.1 (π x * π g)) = e (f.1 (π (x * g)))
    rw [map_mul])

end CoindInflation

end Langlands.FiniteRep

namespace Langlands.FiniteRepresentation

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A representation acting trivially on an open subgroup is continuous. -/
theorem isContinuous_of_le_ker (A : FiniteRepresentation.{0, uG, uV} ℂ G) (N : Subgroup G)
    (hN : IsOpen (N : Set G)) (h : ∀ n ∈ N, A.representation n = 1) : A.IsContinuous := by
  let : TopologicalSpace (Module.End ℂ A) := moduleTopology ℂ (Module.End ℂ A)
  exact Weil.continuous_of_open_kernel A.representation
    (Subgroup.isOpen_mono (fun n hn => (MonoidHom.mem_ker).mpr (h n hn)) hN)

variable {Q : Type uQ} [Group Q]

/-- Inflation of a finite coordinate representation of `Q` along `π`, with its
carrier lifted to the universe `uV`. -/
def inflate (π : G →* Q) (V : FDRep ℂ Q) : FiniteRepresentation.{0, uG, uV} ℂ G :=
  restrict π (VirtualRepresentation.Weil.liftFiniteRepresentation.{uQ, uV} V)

/-- Inflation along a homomorphism with open kernel is continuous. -/
theorem isContinuous_inflate (π : G →* Q) (hπ : IsOpen (π.ker : Set G)) (V : FDRep ℂ Q) :
    (inflate.{uG, uQ, uV} π V).IsContinuous :=
  isContinuous_of_le_ker _ π.ker hπ (fun n hn => by
    change (VirtualRepresentation.Weil.liftFiniteRepresentation.{uQ, uV} V).representation
      (π n) = 1
    rw [(MonoidHom.mem_ker).mp hn, map_one])

/-- An equivalence of representations of `Q` stays an equivalence after composing
with `π`. -/
def _root_.Langlands.FiniteRep.compEquiv {k : Type*} [CommRing k] {H J : Type*} [Monoid H]
    [Monoid J] {X Y : Type*} [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    (φ : H →* J) {ρ : Representation k J X} {σ : Representation k J Y}
    (e : Representation.Equiv ρ σ) : Representation.Equiv (ρ.comp φ) (σ.comp φ) :=
  Representation.Equiv.mk e.toLinearEquiv (fun h => e.isIntertwining' (φ h))

/-- The inflation of `V` is equivalent to any representation equivalent to `V`,
composed with `π`. -/
def inflateEquiv (π : G →* Q) (V : FDRep ℂ Q) {X : Type*} [AddCommGroup X] [Module ℂ X]
    {ρ : Representation ℂ Q X} (e : Representation.Equiv V.ρ ρ) :
    Representation.Equiv (inflate.{uG, uQ, uV} π V).representation (ρ.comp π) :=
  (FiniteRep.compEquiv π (VirtualRepresentation.Weil.liftFiniteEquiv.{uQ, uV} V)).symm.trans
    (FiniteRep.compEquiv π e)

end Langlands.FiniteRepresentation

namespace Langlands.VirtualRepresentation.ExactGrothendieckGroup

/-- A representation equivalent to a product has the sum class. -/
theorem ofRepresentation_eq_add_of_equiv_prod {K : Type*} [Field K] {G : Type uG} [Monoid G]
    (P : FiniteRepresentation.{_, uG, uV} K G → Prop)
    (A B C : {A : FiniteRepresentation.{_, uG, uV} K G // P A})
    (e : Representation.Equiv C.val.representation
      (A.val.representation.prod B.val.representation)) :
    ofRepresentation P C = ofRepresentation P A + ofRepresentation P B := by
  let ℓ := e.toLinearEquiv
  refine ofRepresentation_shortExact P
    (f := e.symm.toIntertwiningMap.comp (Representation.IntertwiningMap.inl K _ _))
    (g := (Representation.IntertwiningMap.snd K _ _).comp e.toIntertwiningMap) ⟨?_, ?_, ?_⟩
  · intro x y h
    have h' := congrArg (fun c => (ℓ c).1) h
    change (ℓ (ℓ.symm (x, 0))).1 = (ℓ (ℓ.symm (y, 0))).1 at h'
    simpa only [LinearEquiv.apply_symm_apply] using h'
  · intro b
    refine ⟨ℓ.symm (0, b), ?_⟩
    change (ℓ (ℓ.symm (0, b))).2 = b
    rw [LinearEquiv.apply_symm_apply]
  · ext c
    simp only [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨a, rfl⟩
      change (ℓ (ℓ.symm (a, 0))).2 = 0
      rw [LinearEquiv.apply_symm_apply]
    · intro hc
      change (ℓ c).2 = 0 at hc
      refine ⟨(ℓ c).1, ?_⟩
      have hp : ((ℓ c).1, (0 : B.val)) = ℓ c := Prod.ext rfl hc.symm
      change ℓ.symm ((ℓ c).1, 0) = c
      rw [hp, LinearEquiv.symm_apply_apply]

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Q : Type uQ} [Group Q]

/-- Inflation on genuine representation classes of `Q`. -/
def inflateClass (π : G →* Q) (hπ : IsOpen (π.ker : Set G)) :
    FiniteRep.RepClass ℂ Q →
      ExactGrothendieckGroup (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous) :=
  Quotient.lift
    (fun V => ofRepresentation _ ⟨FiniteRepresentation.inflate.{uG, uQ, uV} π V,
      FiniteRepresentation.isContinuous_inflate π hπ V⟩)
    (fun V W ⟨e⟩ => ofRepresentation_eq_of_equiv _
      ((FiniteRepresentation.inflateEquiv π V (FiniteRep.equivOfIso e)).trans
        (FiniteRepresentation.inflateEquiv π W (Representation.Equiv.refl _)).symm))

theorem inflateClass_classOf (π : G →* Q) (hπ : IsOpen (π.ker : Set G)) (V : FDRep ℂ Q) :
    inflateClass.{uG, uQ, uV} π hπ (FiniteRep.classOf V) =
      ofRepresentation _ ⟨FiniteRepresentation.inflate.{uG, uQ, uV} π V,
        FiniteRepresentation.isContinuous_inflate π hπ V⟩ := rfl

/-- Inflation is additive for direct sums. -/
theorem inflateClass_add (π : G →* Q) (hπ : IsOpen (π.ker : Set G))
    (a b : FiniteRep.RepClass ℂ Q) :
    inflateClass.{uG, uQ, uV} π hπ (a + b) =
      inflateClass π hπ a + inflateClass π hπ b := by
  induction a using Quotient.inductionOn with | h V =>
  induction b using Quotient.inductionOn with | h W =>
  change ofRepresentation _ ⟨FiniteRepresentation.inflate.{uG, uQ, uV} π
      (FiniteRep.sumRep V W), _⟩ =
    ofRepresentation _ ⟨FiniteRepresentation.inflate π V, _⟩ +
      ofRepresentation _ ⟨FiniteRepresentation.inflate π W, _⟩
  exact ofRepresentation_eq_add_of_equiv_prod _ _ _ _
    ((FiniteRepresentation.inflateEquiv π (FiniteRep.sumRep V W)
      (Representation.Equiv.refl _)).trans
      (FiniteRep.prodEquiv
        (FiniteRepresentation.inflateEquiv π V (Representation.Equiv.refl _)).symm
        (FiniteRepresentation.inflateEquiv π W (Representation.Equiv.refl _)).symm))

/-- Inflation as an additive map on genuine representation classes. -/
def inflateHom (π : G →* Q) (hπ : IsOpen (π.ker : Set G)) :
    FiniteRep.RepClass ℂ Q →+
      ExactGrothendieckGroup (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous) :=
  AddMonoidHom.mk' (inflateClass π hπ) (inflateClass_add π hπ)

/-- Inflation from the split Grothendieck group of `Q` to the continuous exact
virtual group of `G`. -/
def inflate (π : G →* Q) (hπ : IsOpen (π.ker : Set G)) :
    FiniteRep.VirtualRep ℂ Q →ₗ[ℤ]
      ExactGrothendieckGroup (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous) :=
  (Algebra.GrothendieckAddGroup.lift (inflateHom π hπ)).toIntLinearMap

@[simp]
theorem inflate_ofClass (π : G →* Q) (hπ : IsOpen (π.ker : Set G))
    (a : FiniteRep.RepClass ℂ Q) :
    inflate.{uG, uQ, uV} π hπ (FiniteRep.ofClass a) = inflateClass π hπ a :=
  FiniteRep.completionLift_of _ a

/-- Inflating an induced class gives the induced class of a representation of the
preimage subgroup matching the original one through `e`. -/
theorem inflate_ofClass_induce (π : G →* Q) (hπ : IsOpen (π.ker : Set G))
    (hsurj : Function.Surjective π) (S : Subgroup Q) [S.FiniteIndex]
    (T : Subgroup G) [T.FiniteIndex] (hT : ∀ g, g ∈ T ↔ π g ∈ S)
    (hP : ∀ A : FiniteRepresentation.{0, uG, uV} ℂ T, A.IsContinuous →
      (FiniteRepresentation.induce T A).IsContinuous)
    (V : FDRep ℂ S) (B : FiniteRepresentation.{0, uG, uV} ℂ T) (hB : B.IsContinuous)
    (e : V ≃ₗ[ℂ] B)
    (he : ∀ (t : T) (v : V), e (V.ρ ⟨π t, (hT t).mp t.2⟩ v) = B.representation t (e v)) :
    inflate.{uG, uQ, max uG uV} π hπ
        (FiniteRep.ofClass (FiniteRep.induce S (FiniteRep.classOf V))) =
      ExactGrothendieckGroup.induce T _ _ hP (ofRepresentation _ ⟨B, hB⟩) := by
  rw [inflate_ofClass, induce_ofRepresentation]
  change ofRepresentation _ ⟨FiniteRepresentation.inflate π (FiniteRep.induceRep S V), _⟩ = _
  apply ofRepresentation_eq_of_equiv
  exact (FiniteRepresentation.inflateEquiv π _
      ((FiniteRep.induceRepEquiv S V).symm.trans (FiniteRep.indCoindEquiv S V))).trans
    (FiniteRep.coindInflationEquiv π S T hT V.ρ B.representation e he hsurj)

end Langlands.VirtualRepresentation.ExactGrothendieckGroup
