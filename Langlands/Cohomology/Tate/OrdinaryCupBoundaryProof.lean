import Langlands.Cohomology.Tate.OrdinaryCupBoundaryStatement

noncomputable section

universe u

open CategoryTheory groupCohomology
open scoped MonoidalCategory TensorProduct

namespace Langlands.Tate.OrdinaryCupBoundary

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G]

lemma cochainCup_naturality {A A' B B' C C' : Rep.{u} R G}
    (φ : Pairing A B C) (φ' : Pairing A' B' C')
    (f : A ⟶ A') (g : B ⟶ B') (h : C ⟶ C')
    (hφ : ∀ a b, h.hom (φ.bilinear a b) = φ'.bilinear (f.hom a) (g.hom b))
    (p q : ℕ) (a : (inhomogeneousCochains A).X p)
    (b : (inhomogeneousCochains B).X q) :
    h.hom ∘ ordinaryCochainCup φ p q a b =
      ordinaryCochainCup φ' p q (f.hom ∘ a) (g.hom ∘ b) := by
  funext x
  calc
    _ = h.hom (φ.bilinear (a fun i => x (Fin.castAdd q i))
        (B.ρ (List.ofFn fun i : Fin p => x (Fin.castAdd q i)).prod
          (b fun j => x (Fin.natAdd p j)))) :=
      congrArg h.hom (ordinaryCochainCup_apply φ p q a b x)
    _ = _ := by
      rw [hφ, Rep.hom_comm_apply]
      exact (ordinaryCochainCup_apply φ' p q (f.hom ∘ a) (g.hom ∘ b) x).symm

lemma delta_cocycle {S : ShortComplex (Rep.{u} R G)} (hS : S.ShortExact)
    {i j : ℕ} (hij : i + 1 = j) (z : cocycles S.X₃ i)
    (y : (inhomogeneousCochains S.X₂).X i)
    (hy : (cochainsMap (MonoidHom.id G) S.g).f i y = iCocycles S.X₃ i z)
    (x : cocycles S.X₁ j)
    (hx : S.f.hom ∘ iCocycles S.X₁ j x = (inhomogeneousCochains S.X₂).d i j y) :
    δ hS i j hij (π S.X₃ i z) = π S.X₁ j x := by
  have hz : (inhomogeneousCochains S.X₃).d i j (iCocycles S.X₃ i z) = 0 :=
    ConcreteCategory.congr_hom ((inhomogeneousCochains S.X₃).iCycles_d i j) z
  have he : cocyclesMk (iCocycles S.X₃ i z) (OrdinaryCup.cocycle_d _ _ z) = z := by
    apply OrdinaryCup.cocycle_ext
    exact iCocycles_mk _ _
  have hd := groupCohomology.δ_apply hS hij (iCocycles S.X₃ i z) hz y hy
    (iCocycles S.X₁ j x) hx
  rw [he] at hd
  refine hd.trans (congrArg (π S.X₁ j) ?_)
  apply OrdinaryCup.cocycle_ext
  exact iCocycles_mk _ _

lemma delta_lift {S : ShortComplex (Rep.{u} R G)} (hS : S.ShortExact)
    (n : ℕ) (z : cocycles S.X₃ n) :
    ∃ (y : (inhomogeneousCochains S.X₂).X n) (x : cocycles S.X₁ (n + 1)),
      (cochainsMap (MonoidHom.id G) S.g).f n y = iCocycles S.X₃ n z ∧
      S.f.hom ∘ iCocycles S.X₁ (n + 1) x =
        (inhomogeneousCochains S.X₂).d n (n + 1) y ∧
      δ hS n (n + 1) rfl (π S.X₃ n z) = π S.X₁ (n + 1) x := by
  let C := S.map (cochainsFunctor R G)
  have hC := map_cochainsFunctor_shortExact hS
  have he (i : ℕ) := hC.map_of_exact (HomologicalComplex.eval (ModuleCat R) (.up ℕ) i)
  obtain ⟨y, hy⟩ := (he n).moduleCat_surjective_g (iCocycles S.X₃ n z)
  have hy' : C.g.f n y = iCocycles S.X₃ n z := hy
  have hdy : C.g.f (n + 1) (C.X₂.d n (n + 1) y) = 0 := by
    rw [← ModuleCat.comp_apply, ← C.g.comm, ModuleCat.comp_apply, hy']
    exact ConcreteCategory.congr_hom (C.X₃.iCycles_d n (n + 1)) z
  obtain ⟨x, hx⟩ := (ShortComplex.moduleCat_exact_iff _).mp (he (n + 1)).exact _ hdy
  have hx' : S.f.hom ∘ x = (inhomogeneousCochains S.X₂).d n (n + 1) y := hx
  let xc := cocyclesMkOfCompEqD hS hx'
  have hxc : S.f.hom ∘ iCocycles S.X₁ (n + 1) xc =
      (inhomogeneousCochains S.X₂).d n (n + 1) y := by
    rw [iCocycles_mk]
    exact hx'
  exact ⟨y, xc, hy, hxc, delta_cocycle hS rfl z y hy xc hxc⟩

lemma delta_degree {S : ShortComplex (Rep.{u} R G)} (hS : S.ShortExact)
    (i j : ℕ) (h : i + 1 = j) (a : groupCohomology S.X₃ i) :
    (eqToIso (congrArg (groupCohomology S.X₁) h)).hom (δ hS i (i + 1) rfl a) =
      δ hS i j h a := by
  subst j
  rfl

lemma tensorRight_cochain {A A' : Rep.{u} R G} (f : A ⟶ A') (B : Rep.{u} R G)
    (p q : ℕ) (a : (inhomogeneousCochains A).X p)
    (b : (inhomogeneousCochains B).X q) :
    (f ▷ B).hom ∘ ordinaryCochainCup (tensorPairing A B) p q a b =
      ordinaryCochainCup (tensorPairing A' B) p q (f.hom ∘ a) b := by
  exact cochainCup_naturality (tensorPairing A B) (tensorPairing A' B) f (𝟙 B) (f ▷ B)
    (fun a b => TensorProduct.map_tmul _ _ a b) p q a b

lemma tensorLeft_cochain (A : Rep.{u} R G) {B B' : Rep.{u} R G} (f : B ⟶ B')
    (p q : ℕ) (a : (inhomogeneousCochains A).X p)
    (b : (inhomogeneousCochains B).X q) :
    (A ◁ f).hom ∘ ordinaryCochainCup (tensorPairing A B) p q a b =
      ordinaryCochainCup (tensorPairing A B') p q a (f.hom ∘ b) := by
  exact cochainCup_naturality (tensorPairing A B) (tensorPairing A B') (𝟙 A) f (A ◁ f)
    (fun a b => TensorProduct.map_tmul _ _ a b) p q a b

lemma tensor_left_boundary {S : ShortComplex (Rep.{u} R G)} (hS : S.ShortExact)
    (B : Rep.{u} R G) (hB : (S.map (MonoidalCategory.tensorRight B)).ShortExact)
    (p q : ℕ) (a : groupCohomology S.X₃ p) (b : groupCohomology B q) :
    ordinaryCup (tensorPairing S.X₁ B) (p + 1) q (δ hS p (p + 1) rfl a) b =
      (eqToIso (congrArg (groupCohomology (S.X₁ ⊗ B))
        (show (p + q) + 1 = (p + 1) + q by omega))).hom
          (δ hB (p + q) ((p + q) + 1) rfl
            (ordinaryCup (tensorPairing S.X₃ B) p q a b)) := by
  obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective (π S.X₃ p)).mp inferInstance a
  obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective (π B q)).mp inferInstance b
  obtain ⟨y, x, hy, hx, hd⟩ := delta_lift hS p a
  rw [hd, ordinaryCup_π_π, ordinaryCup_π_π]
  refine Eq.trans ?_ (delta_degree hB (p + q) ((p + 1) + q) (by omega)
    (π (S.X₃ ⊗ B) (p + q) (ordinaryCupCocycles (tensorPairing S.X₃ B) p q a b))).symm
  symm
  apply delta_cocycle hB (by omega) (ordinaryCupCocycles (tensorPairing S.X₃ B) p q a b)
    (ordinaryCochainCup (tensorPairing S.X₂ B) p q y (iCocycles B q b))
  · change (S.g ▷ B).hom ∘ ordinaryCochainCup (tensorPairing S.X₂ B) p q y
        (iCocycles B q b) = _
    rw [tensorRight_cochain]
    have hy' : S.g.hom ∘ y = iCocycles S.X₃ p a := hy
    rw [hy']
    exact (i_ordinaryCupCocycles (tensorPairing S.X₃ B) p q a b).symm
  · change (S.f ▷ B).hom ∘ iCocycles (S.X₁ ⊗ B) ((p + 1) + q)
        (ordinaryCupCocycles (tensorPairing S.X₁ B) (p + 1) q x b) =
      (inhomogeneousCochains (S.X₂ ⊗ B)).d (p + q) ((p + 1) + q)
        (ordinaryCochainCup (tensorPairing S.X₂ B) p q y (iCocycles B q b))
    rw [i_ordinaryCupCocycles, tensorRight_cochain, hx,
      groupCohomology.inhomogeneousCochains.d_def,
      OrdinaryCup.differential_eq_transport _ _ _ (by omega), ordinaryCochainCup_d,
      OrdinaryCup.cocycle_d, map_zero, smul_zero, add_zero,
      OrdinaryCup.transport_trans, OrdinaryCup.transport_rfl]

lemma coefficient_smul {A B : Rep.{u} R G} (f : A ⟶ B) (r : R) (n : ℕ)
    (x : (inhomogeneousCochains A).X n) :
    f.hom ∘ (r • x) = r • (f.hom ∘ x) := by
  funext t
  exact map_smul f.hom r (x t)

lemma tensor_right_boundary {S : ShortComplex (Rep.{u} R G)} (hS : S.ShortExact)
    (A : Rep.{u} R G) (hA : (S.map (MonoidalCategory.tensorLeft A)).ShortExact)
    (p q : ℕ) (a : groupCohomology A p) (b : groupCohomology S.X₃ q) :
    ordinaryCup (tensorPairing A S.X₁) p (q + 1) a (δ hS q (q + 1) rfl b) =
      (-1 : R) ^ p •
        (eqToIso (congrArg (groupCohomology (A ⊗ S.X₁))
          (show (p + q) + 1 = p + (q + 1) by omega))).hom
            (δ hA (p + q) ((p + q) + 1) rfl
              (ordinaryCup (tensorPairing A S.X₃) p q a b)) := by
  obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective (π A p)).mp inferInstance a
  obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective (π S.X₃ q)).mp inferInstance b
  obtain ⟨y, x, hy, hx, hd⟩ := delta_lift hS q b
  rw [hd, ordinaryCup_π_π, ordinaryCup_π_π]
  have hdB : δ hA (p + q) (p + (q + 1)) (by omega)
      (π (A ⊗ S.X₃) (p + q) (ordinaryCupCocycles (tensorPairing A S.X₃) p q a b)) =
      (-1 : R) ^ p • π (A ⊗ S.X₁) (p + (q + 1))
        (ordinaryCupCocycles (tensorPairing A S.X₁) p (q + 1) a x) := by
    refine Eq.trans (delta_cocycle hA (by omega)
      (ordinaryCupCocycles (tensorPairing A S.X₃) p q a b)
      (ordinaryCochainCup (tensorPairing A S.X₂) p q (iCocycles A p a) y) ?_
      ((-1 : R) ^ p • ordinaryCupCocycles (tensorPairing A S.X₁) p (q + 1) a x) ?_)
      (map_smul (π (A ⊗ S.X₁) (p + (q + 1))).hom _ _)
    · change (A ◁ S.g).hom ∘ ordinaryCochainCup (tensorPairing A S.X₂) p q
          (iCocycles A p a) y = _
      rw [tensorLeft_cochain]
      have hy' : S.g.hom ∘ y = iCocycles S.X₃ q b := hy
      rw [hy']
      exact (i_ordinaryCupCocycles (tensorPairing A S.X₃) p q a b).symm
    · change (A ◁ S.f).hom ∘ iCocycles (A ⊗ S.X₁) (p + (q + 1))
          ((-1 : R) ^ p • ordinaryCupCocycles (tensorPairing A S.X₁) p (q + 1) a x) =
        (inhomogeneousCochains (A ⊗ S.X₂)).d (p + q) (p + (q + 1))
          (ordinaryCochainCup (tensorPairing A S.X₂) p q (iCocycles A p a) y)
      rw [map_smul, coefficient_smul, i_ordinaryCupCocycles, tensorLeft_cochain, hx,
        groupCohomology.inhomogeneousCochains.d_def,
        OrdinaryCup.differential_eq_transport _ _ _ (by omega), ordinaryCochainCup_d,
        OrdinaryCup.cocycle_d]
      have hz : ordinaryCochainCup (tensorPairing A S.X₂) (p + 1) q 0 y = 0 :=
        LinearMap.congr_fun (map_zero (ordinaryCochainCup (tensorPairing A S.X₂) (p + 1) q)) y
      rw [hz, map_zero, zero_add]
      exact (OrdinaryCup.transport_rfl (A ⊗ S.X₂) (p + (q + 1)) _).symm
  have ht := delta_degree hA (p + q) (p + (q + 1)) (by omega)
    (π (A ⊗ S.X₃) (p + q) (ordinaryCupCocycles (tensorPairing A S.X₃) p q a b))
  have hs : (-1 : R) ^ p * (-1 : R) ^ p = 1 := by
    rw [← mul_pow]
    simp
  calc
    _ = (-1 : R) ^ p • ((-1 : R) ^ p • π (A ⊗ S.X₁) (p + (q + 1))
        (ordinaryCupCocycles (tensorPairing A S.X₁) p (q + 1) a x)) := by
      rw [smul_smul, hs, one_smul]
    _ = _ := congrArg (fun c => (-1 : R) ^ p • c) (ht.trans hdB).symm

end Langlands.Tate.OrdinaryCupBoundary

namespace Langlands.Tate

/-- The two connecting-map signs of the actual ordinary tensor cup. -/
theorem ordinaryCupBoundaryLaws : OrdinaryCupBoundaryLaws.{u} := by
  intro R G _ _
  exact ⟨fun S hS B hB p q a b =>
      OrdinaryCupBoundary.tensor_left_boundary hS B hB p q a b,
    fun S hS A hA p q a b =>
      OrdinaryCupBoundary.tensor_right_boundary hS A hA p q a b⟩

end Langlands.Tate
