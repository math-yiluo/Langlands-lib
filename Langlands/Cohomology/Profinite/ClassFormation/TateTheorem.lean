import Langlands.Cohomology.Profinite.Cup.Inflation
import Langlands.Cohomology.Tate.OrdinaryTateCupProof
import Langlands.Cohomology.Tate.TateTheoremProof

/-!
# Tate's theorem in the form used by class formations

For a finite group `Γ`, a representation `M` over the integers (the Library's `IntegralScalar`)
and a class `u ∈ H²(Γ, M)` whose restriction to every subgroup `S` generates `H²(S, M)`, has
order `|S|`, and with `H¹(S, M) = 0`, every class of `H^{n+2}(Γ, M)` (`n ≥ 1`) is the cup product
of `u` with a class of `Hⁿ(Γ, ℤ)` killed by an integer `m ≠ 0`. This is the Library's
`Langlands.Tate.tateCupIsomorphism` (bijectivity of cup with `u` on Tate cohomology), read in positive
degree through the comparison `Langlands.Tate.ordinaryToTate` and the agreement of the ordinary and
the Tate cup products.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory groupCohomology Langlands.Tate

namespace Langlands.ProfiniteCohomology.GroupCoh

variable {Γ : Type u} [Group Γ] [Fintype Γ]

theorem ordinaryToTate_eqToHom (A : Rep.{u} IntegralScalar.{u} Γ) {m m' : ℕ} (h : m = m')
    (x : groupCohomology A m) :
    ordinaryToTate A m' ((eqToHom (congrArg (groupCohomology A) h)).hom x) =
      (tateDegreeIso A (congrArg Nat.cast h)).hom (ordinaryToTate A m x) := by
  subst h
  simp [tateDegreeIso]

theorem ordinaryToTate_injective_of_neZero (A : Rep.{u} IntegralScalar.{u} Γ) (n : ℕ) [NeZero n] :
    Function.Injective (ordinaryToTate A n) := by
  rw [ordinaryToTate_pos]
  exact ((TateCohomology.isoGroupCohomology (R := IntegralScalar.{u}) (G := Γ) n).app A).symm
    |>.toLinearEquiv.injective

theorem map_eqToHom_groupCohomology {A B : Rep.{u} IntegralScalar.{u} Γ} (f : A ⟶ B) {m m' : ℕ}
    (h : m = m') (x : groupCohomology A m) :
    groupCohomology.map (MonoidHom.id Γ) f m'
        ((eqToHom (congrArg (groupCohomology A) h)).hom x) =
      (eqToHom (congrArg (groupCohomology B) h)).hom
        (groupCohomology.map (MonoidHom.id Γ) f m x) := by
  subst h
  simp

/-- The cup product for the scalar pairing `A × k → A` is the image of the cup product for the
tensor pairing under the right unitor. -/
theorem ordinaryCup_scalarPairing (A : Rep.{u} IntegralScalar.{u} Γ) (p q : ℕ)
    (a : groupCohomology A p)
    (b : groupCohomology (Rep.trivial IntegralScalar.{u} Γ IntegralScalar.{u}) q) :
    ordinaryCup (scalarPairing A) p q a b =
      groupCohomology.map (MonoidHom.id Γ) (ρ_ A).hom (p + q)
        (ordinaryCup (tensorPairing A (Rep.trivial IntegralScalar.{u} Γ IntegralScalar.{u}))
          p q a b) := by
  have h := (ordinaryCupLaws IntegralScalar.{u} Γ).2 A A
    (Rep.trivial IntegralScalar.{u} Γ IntegralScalar.{u})
    (Rep.trivial IntegralScalar.{u} Γ IntegralScalar.{u}) (A ⊗ Rep.trivial _ Γ _) A
    (tensorPairing A _) (scalarPairing A) (𝟙 A) (𝟙 _) (ρ_ A).hom (fun _ _ => rfl) p q a b
  rw [h]
  simp

/-- Tate's theorem, in positive degree and for the ordinary cup product: under Tate's conditions
on all subgroups, every class of `H^{n+2}(Γ, M)` (`n ≥ 1`) is `u ∪ y` (through the right unitor)
for some class `y ∈ Hⁿ(Γ, ℤ)` killed by a nonzero integer. -/
theorem exists_cupH_of_tate (M : Rep.{u} IntegralScalar.{u} Γ) (u : groupCohomology M 2)
    (h1 : ∀ S : Subgroup Γ, Limits.IsZero (groupCohomology (Rep.res S.subtype M) 1))
    (h2 : ∀ S : Subgroup Γ,
      addOrderOf (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype M)) 2 u) = Nat.card S)
    (h3 : ∀ (S : Subgroup Γ) (y : groupCohomology (Rep.res S.subtype M) 2),
      ∃ m : ℤ, y = m • groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype M)) 2 u)
    (n : ℕ) [NeZero n] (x : groupCohomology M (n + 2)) :
    ∃ y : groupCohomology (Rep.trivial IntegralScalar.{u} Γ IntegralScalar.{u}) n,
      (∃ m : ℕ, m ≠ 0 ∧ m • y = 0) ∧
        x = groupCohomology.map (MonoidHom.id Γ) (ρ_ M).hom (n + 2) (cupH (add_comm 2 n) u y) := by
  -- Tate's conditions on the Sylow subgroups
  have hsyl : ∀ (p : ℕ), p.Prime → ∀ P : Sylow p Γ,
      Subsingleton (groupCohomology (Rep.res P.1.subtype M) 1) ∧
        Nat.card (groupCohomology (Rep.res P.1.subtype M) 2) = Nat.card P ∧
        AddSubgroup.zmultiples
          (groupCohomology.map P.1.subtype (𝟙 (Rep.res P.1.subtype M)) 2 u) = ⊤ := by
    intro p _ P
    have htop : AddSubgroup.zmultiples
        (groupCohomology.map P.1.subtype (𝟙 (Rep.res P.1.subtype M)) 2 u) = ⊤ := by
      refine eq_top_iff.2 fun y _ => ?_
      obtain ⟨m, hm⟩ := h3 P.1 y
      exact ⟨m, hm.symm⟩
    refine ⟨ModuleCat.subsingleton_of_isZero (h1 P.1), ?_, htop⟩
    rw [← h2 P.1, ← Nat.card_zmultiples, htop, AddSubgroup.card_top]
  have hT := tateCupIsomorphism Γ M u hsyl (n : ℤ)
  have hn : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
  obtain ⟨z, hz⟩ := hT.2 ((tateDegreeIso M hn).hom (ordinaryToTate M (n + 2) x))
  obtain ⟨y, rfl⟩ := ordinaryToTate_surjective
    (Rep.trivial IntegralScalar.{u} Γ IntegralScalar.{u}) n z
  refine ⟨y, ⟨Fintype.card Γ, Fintype.card_ne_zero,
    card_smul_groupCohomology _ (NeZero.ne n) y⟩, ?_⟩
  apply ordinaryToTate_injective_of_neZero M (n + 2)
  apply (tateDegreeIso M hn).toLinearEquiv.injective
  change (tateDegreeIso M hn).hom.hom (ordinaryToTate M (n + 2) x) = _
  rw [← hz]
  -- the right-hand side, through the comparison of cup products
  have hcup : cupH (add_comm 2 n) u y =
      (eqToHom (congrArg (groupCohomology (M ⊗ Rep.trivial IntegralScalar.{u} Γ IntegralScalar.{u}))
        (add_comm 2 n))).hom
        (ordinaryCup (tensorPairing M (Rep.trivial IntegralScalar.{u} Γ IntegralScalar.{u}))
          2 n u y) := rfl
  rw [hcup, map_eqToHom_groupCohomology, ← ordinaryCup_scalarPairing, ordinaryToTate_eqToHom]
  have hlaw := ordinaryTateCupLaws IntegralScalar.{u} Γ M
    (Rep.trivial IntegralScalar.{u} Γ IntegralScalar.{u}) M (scalarPairing M) 2 n u y
  have h2u :
      ((TateCohomology.isoGroupCohomology (R := IntegralScalar.{u}) (G := Γ) 2).app M).symm.toLinearEquiv
        u = ordinaryToTate M 2 u := by
    rw [ordinaryToTate_pos]
    rfl
  change (tateDegreeIso M (add_comm 2 (n : ℤ))).toLinearEquiv
      (Langlands.Tate.cup (scalarPairing M) 2 n
        (((TateCohomology.isoGroupCohomology 2).app M).symm.toLinearEquiv u)
        (ordinaryToTate (Rep.trivial IntegralScalar.{u} Γ IntegralScalar.{u}) n y)) = _
  rw [h2u]
  erw [← hlaw]
  simp only [tateDegreeIso, Iso.toLinearEquiv_apply, eqToIso.hom, ← ConcreteCategory.comp_apply]
  all_goals first
    | omega
    | simp only [Category.assoc, eqToHom_trans]

end Langlands.ProfiniteCohomology.GroupCoh
