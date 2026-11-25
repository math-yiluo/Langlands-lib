import Langlands.GaloisCohomology.CompactSupport.Functoriality
import Langlands.GaloisCohomology.CompactSupport.Internal.ConeSigns
import Langlands.Cohomology.Profinite.Duality.Pairing

/-!
# Cup products on cohomology with compact support

With the notation of `Basic.lean`, a morphism `μ : A ⊗ B ⟶ C` of `G`-modules with local pairings
`μ_v : A_v ⊗ Res B ⟶ C_v` compatible with `a`, `c` gives the cup product
`H_c^r(G, A) × Hˢ(G, B) → H_c^{r+s}(G, C)` (`compactCup`); symmetrically `compactCupRight` for compact
support in the right factor. The cup product is compatible with `localToCompact`
(`compactCup_localToCompact`: `∂(ξ) ∪ z = ∂((ξ_v ∪ res_v z)_v)`), the two versions agree on classes of
`H_c` paired with images of classes of `H_c` (`compactCup_eq_compactCupRight`), and the cup product
commutes with connecting maps up to the sign `(-1)ʳ` (`compactCup_compactSupportδ_add_compactCup_δ`).
-/

namespace Langlands.GaloisCohomology

open Langlands Langlands.ProfiniteCohomology

universe u

-- from CompactSupportCohomology/CompactCupEqCompactCupRight.lean
section CompactCupEqCompactCupRight

open CategoryTheory Limits MonoidalCategory Langlands.ProfiniteCohomology.GroupCoh


variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)

section Left

variable {A B C : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B] [IsSmoothRep C]
  {Aᵥ Cᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsSmoothRep (Aᵥ v)] [∀ v, IsSmoothRep (Cᵥ v)]
  {a : ∀ v, Rep.res (φ v : H v →* G) A ⟶ Aᵥ v} {c : ∀ v, Rep.res (φ v : H v →* G) C ⟶ Cᵥ v}

/-- The Leibniz pairing `C_c•(G, A) × C•(G, B) → C_c•(G, C)` induced by `μ : A ⊗ B ⟶ C` and
compatible local pairings `μ_v`. -/
noncomputable def compactCupLeibniz (μ : A ⊗ B ⟶ C)
    (μᵥ : ∀ v, Aᵥ v ⊗ Rep.res (φ v : H v →* G) B ⟶ Cᵥ v)
    (hμ : ∀ v, (Rep.resFunctor (φ v : H v →* G)).map μ ≫ c v =
      resTensorHom (φ v : H v →* G) (a v) (𝟙 _) ≫ μᵥ v) :
    LeibnizPairing (compactSupportCochains φ A Aᵥ a) (cochains B) (compactSupportCochains φ C Cᵥ c) :=
  LeibnizPairing.coconeLeft (LeibnizPairing.pi fun v => cupLeibniz (μᵥ v))
    (localRes φ B (fun v => Rep.res (φ v : H v →* G) B) fun _ => 𝟙 _) (cupLeibniz μ)
    (localRes_cupPairingCochains φ μ μᵥ hμ)

/-- The cup product `H_c^r(G, A) × Hˢ(G, B) → H_c^{r+s}(G, C)` along `μ : A ⊗ B ⟶ C` and
compatible local pairings `μ_v : A_v ⊗ Res B ⟶ C_v`. -/
noncomputable def compactCup (μ : A ⊗ B ⟶ C)
    (μᵥ : ∀ v, Aᵥ v ⊗ Rep.res (φ v : H v →* G) B ⟶ Cᵥ v)
    (hμ : ∀ v, (Rep.resFunctor (φ v : H v →* G)).map μ ≫ c v =
      resTensorHom (φ v : H v →* G) (a v) (𝟙 _) ≫ μᵥ v) {r s n : ℕ} (h : r + s = n) :
    compactSupportCohomology φ A Aᵥ a r →ₗ[k] cohomology B s →ₗ[k] compactSupportCohomology φ C Cᵥ c n :=
  (compactCupLeibniz φ μ μᵥ hμ).homology h

variable (μ : A ⊗ B ⟶ C) (μᵥ : ∀ v, Aᵥ v ⊗ Rep.res (φ v : H v →* G) B ⟶ Cᵥ v)
  (hμ : ∀ v, (Rep.resFunctor (φ v : H v →* G)).map μ ≫ c v =
    resTensorHom (φ v : H v →* G) (a v) (𝟙 _) ≫ μᵥ v)

/-- `localToCompact(ξ) ∪ z = localToCompact((ξ_v ∪ res_v z)_v)`. -/
theorem compactCup_localToCompact {r s n : ℕ} (h : r + s = n) (h' : r + 1 + s = n + 1)
    (ξ : ∀ v, cohomology (Aᵥ v) r) (z : cohomology B s) :
    compactCup φ μ μᵥ hμ h' ((localToCompact φ A Aᵥ a r).hom ξ) z =
      (localToCompact φ C Cᵥ c n).hom (fun v => cupPairing (μᵥ v) h (ξ v)
        ((map (φ v) (𝟙 _) s).hom z)) := by
  change (compactCupLeibniz φ μ μᵥ hμ).homology h'
      ((mappingCoconeNat.homologyδ (localRes φ A Aᵥ a) r).hom
        ((localCohomologyIso Aᵥ r).inv.hom ξ)) z =
    (mappingCoconeNat.homologyδ (localRes φ C Cᵥ c) n).hom
      ((localCohomologyIso Cᵥ n).inv.hom _)
  refine (LeibnizPairing.coconeLeft_homology_homologyδ (LeibnizPairing.pi fun v => cupLeibniz (μᵥ v))
    (localRes φ B (fun v => Rep.res (φ v : H v →* G) B) fun _ => 𝟙 _) (cupLeibniz μ)
    (localRes_cupPairingCochains φ μ μᵥ hμ) h h' _ z).trans ?_
  congr 1
  apply (ModuleCat.mono_iff_injective (localCohomologyIso Cᵥ n).hom).1 inferInstance
  rw [hom_apply_hom_apply_of_comp_eq (localCohomologyIso Cᵥ n).inv_hom_id]
  funext v
  refine (LeibnizPairing.piHomologyIso_hom_pi_homology (fun v => cupLeibniz (μᵥ v)) h _ _ v).trans ?_
  refine (cupLeibniz_homology (μᵥ v) h _ _).trans ?_
  exact congrArg₂ (fun p q => cupPairing (μᵥ v) h p q)
    (congrFun (hom_apply_hom_apply_of_comp_eq (localCohomologyIso Aᵥ r).inv_hom_id ξ) v)
    (congrFun (ConcreteCategory.congr_hom (homologyMap_piLift_piHomologyIso_hom _
      (fun v => cochainsMap (φ v)
        (𝟙 (Rep.res (φ v : H v →* G) B))) s) z) v)

end Left

section Right

variable {A B C : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B] [IsSmoothRep C]
  {Bᵥ Cᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsSmoothRep (Bᵥ v)] [∀ v, IsSmoothRep (Cᵥ v)]
  {b : ∀ v, Rep.res (φ v : H v →* G) B ⟶ Bᵥ v} {c : ∀ v, Rep.res (φ v : H v →* G) C ⟶ Cᵥ v}

/-- The Leibniz pairing `C•(G, A) × C_c•(G, B) → C_c•(G, C)` (compact support in the right
factor). -/
noncomputable def compactCupRightLeibniz (μ : A ⊗ B ⟶ C)
    (μᵥ' : ∀ v, Rep.res (φ v : H v →* G) A ⊗ Bᵥ v ⟶ Cᵥ v)
    (hμ' : ∀ v, (Rep.resFunctor (φ v : H v →* G)).map μ ≫ c v =
      resTensorHom (φ v : H v →* G) (𝟙 _) (b v) ≫ μᵥ' v) :
    LeibnizPairing (cochains A) (compactSupportCochains φ B Bᵥ b) (compactSupportCochains φ C Cᵥ c) :=
  LeibnizPairing.coconeRight (LeibnizPairing.pi fun v => cupLeibniz (μᵥ' v))
    (localRes φ A (fun v => Rep.res (φ v : H v →* G) A) fun _ => 𝟙 _) (cupLeibniz μ)
    (localRes_cupPairingCochains φ μ μᵥ' hμ')

/-- The cup product `Hʳ(G, A) × H_c^s(G, B) → H_c^{r+s}(G, C)`. -/
noncomputable def compactCupRight (μ : A ⊗ B ⟶ C)
    (μᵥ' : ∀ v, Rep.res (φ v : H v →* G) A ⊗ Bᵥ v ⟶ Cᵥ v)
    (hμ' : ∀ v, (Rep.resFunctor (φ v : H v →* G)).map μ ≫ c v =
      resTensorHom (φ v : H v →* G) (𝟙 _) (b v) ≫ μᵥ' v) {r s n : ℕ} (h : r + s = n) :
    cohomology A r →ₗ[k] compactSupportCohomology φ B Bᵥ b s →ₗ[k] compactSupportCohomology φ C Cᵥ c n :=
  (compactCupRightLeibniz φ μ μᵥ' hμ').homology h

end Right

section Symmetry

variable {A B C : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B] [IsSmoothRep C]
  {Aᵥ Bᵥ Cᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsSmoothRep (Aᵥ v)] [∀ v, IsSmoothRep (Bᵥ v)]
  [∀ v, IsSmoothRep (Cᵥ v)] {a : ∀ v, Rep.res (φ v : H v →* G) A ⟶ Aᵥ v}
  {b : ∀ v, Rep.res (φ v : H v →* G) B ⟶ Bᵥ v} {c : ∀ v, Rep.res (φ v : H v →* G) C ⟶ Cᵥ v}
  (μ : A ⊗ B ⟶ C) (μᵥ : ∀ v, Aᵥ v ⊗ Rep.res (φ v : H v →* G) B ⟶ Cᵥ v)
  (μᵥ' : ∀ v, Rep.res (φ v : H v →* G) A ⊗ Bᵥ v ⟶ Cᵥ v) (μᵥ'' : ∀ v, Aᵥ v ⊗ Bᵥ v ⟶ Cᵥ v)
  (hμ : ∀ v, (Rep.resFunctor (φ v : H v →* G)).map μ ≫ c v =
    resTensorHom (φ v : H v →* G) (a v) (𝟙 _) ≫ μᵥ v)
  (hμ' : ∀ v, (Rep.resFunctor (φ v : H v →* G)).map μ ≫ c v =
    resTensorHom (φ v : H v →* G) (𝟙 _) (b v) ≫ μᵥ' v)

/-- Cup products of cochains along `ν` and along `ν'` with `ν = (𝟙 ⊗ β) ≫ ν'` agree after applying
`β` to the right factor. -/
theorem cupCochain_tensorHom_eq {K : Type u} [Group K] {X Y Y' Z : Rep.{u} k K}
    (ν : X ⊗ Y ⟶ Z) (ν' : X ⊗ Y' ⟶ Z) (β : Y ⟶ Y') (hν : ν = (𝟙 X ⊗ₘ β) ≫ ν') {r s n : ℕ}
    (h : r + s = n) (f : (Fin r → K) → X) (g : (Fin s → K) → Y) (σ : Fin n → K) :
    ν.hom (cupCochain h f g σ) = ν'.hom (cupCochain h f (fun τ => β.hom (g τ)) σ) := by
  subst hν
  exact congrArg ν'.hom (tensorHom_cupCochain (𝟙 X) β h f g σ)

/-- Cup products of cochains along `ν` and along `ν'` with `ν = (α ⊗ 𝟙) ≫ ν'` agree after applying
`α` to the left factor. -/
theorem cupCochain_tensorHom_eq' {K : Type u} [Group K] {X X' Y Z : Rep.{u} k K}
    (ν : X ⊗ Y ⟶ Z) (ν' : X' ⊗ Y ⟶ Z) (α : X ⟶ X') (hν : ν = (α ⊗ₘ 𝟙 Y) ≫ ν') {r s n : ℕ}
    (h : r + s = n) (f : (Fin r → K) → X) (g : (Fin s → K) → Y) (σ : Fin n → K) :
    ν.hom (cupCochain h f g σ) = ν'.hom (cupCochain h (fun τ => α.hom (f τ)) g σ) := by
  subst hν
  exact congrArg ν'.hom (tensorHom_cupCochain α (𝟙 Y) h f g σ)

/-- For `x ∈ H_c^r(A)`, `y ∈ H_c^s(B)`: `x ∪ (image of y in Hˢ(B)) = (image of x in Hʳ(A)) ∪ y`. -/
theorem compactCup_eq_compactCupRight (hL : ∀ v, μᵥ v = (𝟙 _ ⊗ₘ b v) ≫ μᵥ'' v)
    (hR : ∀ v, μᵥ' v = (a v ⊗ₘ 𝟙 _) ≫ μᵥ'' v) {r s n : ℕ} (h : r + s = n)
    (x : compactSupportCohomology φ A Aᵥ a r) (y : compactSupportCohomology φ B Bᵥ b s) :
    compactCup φ μ μᵥ hμ h x ((compactToGlobal φ B Bᵥ b s).hom y) =
      compactCupRight φ μ μᵥ' hμ' h ((compactToGlobal φ A Aᵥ a r).hom x) y :=
  LeibnizPairing.coconeLeft_homology_eq_coconeRight_homology (fA := localRes φ A Aᵥ a)
    (fB := localRes φ B Bᵥ b) (fC := localRes φ C Cᵥ c)
    (LeibnizPairing.pi fun v => cupLeibniz (μᵥ'' v))
    (localRes φ A (fun v => Rep.res (φ v : H v →* G) A) fun _ => 𝟙 _)
    (localRes φ B (fun v => Rep.res (φ v : H v →* G) B) fun _ => 𝟙 _)
    (LeibnizPairing.pi fun v => cupLeibniz (μᵥ v)) (LeibnizPairing.pi fun v => cupLeibniz (μᵥ' v))
    (fun {_ _ _} h' u y' => funext fun v => cochainOf_injective (funext fun σ =>
      cupCochain_tensorHom_eq (μᵥ v) (μᵥ'' v) (b v) (hL v) h' (cochainOf (Aᵥ v) (u v))
        (fun τ => cochainOf B y' (⇑(φ v : H v →* G) ∘ τ)) σ))
    (fun {_ _ _} h' x' w => funext fun v => cochainOf_injective (funext fun σ =>
      cupCochain_tensorHom_eq' (μᵥ' v) (μᵥ'' v) (a v) (hR v) h'
        (fun τ => cochainOf A x' (⇑(φ v : H v →* G) ∘ τ)) (cochainOf (Bᵥ v) (w v)) σ))
    (cupLeibniz μ) (localRes_cupPairingCochains φ μ μᵥ hμ)
    (localRes_cupPairingCochains φ μ μᵥ' hμ') h x y

end Symmetry

section TwoSequences

variable {SA : ShortComplex (Rep.{u} k G)} [IsSmoothRep SA.X₁] [IsSmoothRep SA.X₂]
  [IsSmoothRep SA.X₃] {SAᵥ : ∀ v, ShortComplex (Rep.{u} k (H v))}
  [∀ v, IsSmoothRep (SAᵥ v).X₁] [∀ v, IsSmoothRep (SAᵥ v).X₂] [∀ v, IsSmoothRep (SAᵥ v).X₃]
  (sA : ∀ v, SA.map (Rep.resFunctor (φ v : H v →* G)) ⟶ SAᵥ v)
  {SB : ShortComplex (Rep.{u} k G)} [IsSmoothRep SB.X₁] [IsSmoothRep SB.X₂]
  [IsSmoothRep SB.X₃] {C : Rep.{u} k G} [IsSmoothRep C] {Cᵥ : ∀ v, Rep.{u} k (H v)}
  [∀ v, IsSmoothRep (Cᵥ v)] {c : ∀ v, Rep.res (φ v : H v →* G) C ⟶ Cᵥ v}
  (μ₁ : SA.X₁ ⊗ SB.X₃ ⟶ C) (μ₂ : SA.X₂ ⊗ SB.X₂ ⟶ C) (μ₃ : SA.X₃ ⊗ SB.X₁ ⟶ C)
  (μ₁ᵥ : ∀ v, (SAᵥ v).X₁ ⊗ Rep.res (φ v : H v →* G) SB.X₃ ⟶ Cᵥ v)
  (μ₂ᵥ : ∀ v, (SAᵥ v).X₂ ⊗ Rep.res (φ v : H v →* G) SB.X₂ ⟶ Cᵥ v)
  (μ₃ᵥ : ∀ v, (SAᵥ v).X₃ ⊗ Rep.res (φ v : H v →* G) SB.X₁ ⟶ Cᵥ v)
  (hμ₁ : ∀ v, (Rep.resFunctor (φ v : H v →* G)).map μ₁ ≫ c v =
    resTensorHom (φ v : H v →* G) (sA v).τ₁ (𝟙 _) ≫ μ₁ᵥ v)
  (hμ₂ : ∀ v, (Rep.resFunctor (φ v : H v →* G)).map μ₂ ≫ c v =
    resTensorHom (φ v : H v →* G) (sA v).τ₂ (𝟙 _) ≫ μ₂ᵥ v)
  (hμ₃ : ∀ v, (Rep.resFunctor (φ v : H v →* G)).map μ₃ ≫ c v =
    resTensorHom (φ v : H v →* G) (sA v).τ₃ (𝟙 _) ≫ μ₃ᵥ v)

include hμ₂ in

/-- Compatibility of the cup product with the connecting maps of two short exact sequences: `δ_c x
∪ y + (-1)ʳ x ∪ δ y = 0`. -/
theorem compactCup_compactSupportδ_add_compactCup_δ
    (h₁₂ : (SA.f ⊗ₘ 𝟙 SB.X₂) ≫ μ₂ = (𝟙 SA.X₁ ⊗ₘ SB.g) ≫ μ₁)
    (h₂₃ : (𝟙 SA.X₂ ⊗ₘ SB.f) ≫ μ₂ = (SA.g ⊗ₘ 𝟙 SB.X₁) ≫ μ₃)
    (h₁₂ᵥ : ∀ v, ((SAᵥ v).f ⊗ₘ 𝟙 _) ≫ μ₂ᵥ v =
      (𝟙 _ ⊗ₘ (Rep.resFunctor (φ v : H v →* G)).map SB.g) ≫ μ₁ᵥ v)
    (h₂₃ᵥ : ∀ v, (𝟙 _ ⊗ₘ (Rep.resFunctor (φ v : H v →* G)).map SB.f) ≫ μ₂ᵥ v =
      ((SAᵥ v).g ⊗ₘ 𝟙 _) ≫ μ₃ᵥ v)
    (hSA : SA.ShortExact) (hSAᵥ : ∀ v, (SAᵥ v).ShortExact) (hSB : SB.ShortExact) {r s n : ℕ}
    (h₁ : r + 1 + s = n + 1) (h₃ : r + (s + 1) = n + 1)
    (x : compactSupportCohomology φ SA.X₃ (fun v => (SAᵥ v).X₃) (fun v => (sA v).τ₃) r)
    (y : cohomology SB.X₃ s) :
    compactCup φ μ₁ μ₁ᵥ hμ₁ h₁ ((compactSupportδ φ sA hSA hSAᵥ r).hom x) y +
      (-1 : k) ^ r • compactCup φ μ₃ μ₃ᵥ hμ₃ h₃ x ((δ hSB s (s + 1) rfl).hom y) = 0 := by
  refine LeibnizPairing.homology_δ_add_homology_δ
    (SM := mappingCoconeNat.mapShortComplex (localResShortComplex φ SA SAᵥ sA))
    (SN := cochainsShortComplex SB) (compactCupLeibniz φ μ₂ μ₂ᵥ hμ₂)
    (compactCupLeibniz φ μ₁ μ₁ᵥ hμ₁) (compactCupLeibniz φ μ₃ μ₃ᵥ hμ₃) ?_ ?_
    (compactSupportCochains_shortExact φ sA hSA hSAᵥ) (cochainsShortComplex_shortExact hSB) h₁ h₃ x y
  · intro r s n h p y
    revert p
    intro (p : (cochains SA.X₁).X r ×
      shiftNegOneX (piComplex fun v => cochains (SAᵥ v).X₁) r)
    obtain ⟨x0, b⟩ := p
    refine Prod.ext ?_ ?_
    · apply cochainOf_injective
      funext σ
      exact cupCochain_pairing_left μ₁ μ₂ h₁₂ h (cochainOf _ x0) (cochainOf _ y) σ
    · cases r with
      | zero => rfl
      | succ r =>
        cases n with
        | zero => rfl
        | succ m =>
          revert b
          intro (b : (piComplex fun v => cochains (SAᵥ v).X₁).X r)
          refine funext fun v => ?_
          apply cochainOf_injective
          funext σ
          exact cupCochain_pairing_left (S := SAᵥ v)
            (T := SB.map (Rep.resFunctor (φ v : H v →* G))) (μ₁ᵥ v) (μ₂ᵥ v) (h₁₂ᵥ v)
            (show r + s = m by omega) (cochainOf _ (b v))
            (fun τ => cochainOf SB.X₂ y (⇑(φ v : H v →* G) ∘ τ)) σ
  · intro r s n h p y
    revert p
    intro (p : (cochains SA.X₂).X r ×
      shiftNegOneX (piComplex fun v => cochains (SAᵥ v).X₂) r)
    obtain ⟨x0, b⟩ := p
    refine Prod.ext ?_ ?_
    · apply cochainOf_injective
      funext σ
      exact cupCochain_pairing_right μ₂ μ₃ h₂₃ h (cochainOf _ x0) (cochainOf _ y) σ
    · cases r with
      | zero => rfl
      | succ r =>
        cases n with
        | zero => rfl
        | succ m =>
          revert b
          intro (b : (piComplex fun v => cochains (SAᵥ v).X₂).X r)
          refine funext fun v => ?_
          apply cochainOf_injective
          funext σ
          exact cupCochain_pairing_right (S := SAᵥ v)
            (T := SB.map (Rep.resFunctor (φ v : H v →* G))) (μ₂ᵥ v) (μ₃ᵥ v) (h₂₃ᵥ v)
            (show r + s = m by omega) (cochainOf _ (b v))
            (fun τ => cochainOf SB.X₁ y (⇑(φ v : H v →* G) ∘ τ)) σ

end TwoSequences

end CompactCupEqCompactCupRight

end Langlands.GaloisCohomology
